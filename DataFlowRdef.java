import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class DataFlowRdef {

//    Make addr_taken a map like Map<Type, Set<VarId>>.
    static Map<String, Set<String>> addressTakenVariables = new TreeMap<>();

    static Map<String, List<String>> typeDefinitions = new HashMap<>();
    static Set<String> allAddressTakenVars = new HashSet<>();

    static Set<String> globalVars = new HashSet<>();
    static Set<String> localParams = new HashSet<>();

    static Map<String, List<ProgramPoint.Instruction>> basicBlocksInstructions = new HashMap<>();

    static Map<String, List<String>> blockSuccessors = new HashMap<>();

    static Map<String, Set<String>> blockVars = new HashMap<>();
    static Map<String, VariableState> variableStates = new TreeMap<>();

    static Map<String, VariableState> fakeHeapStates = new TreeMap<>();

    static Map<String, Set<String>> fnVarTypes = new TreeMap<>();
    static Set<String> processedBlocks = new HashSet<>();

    static TreeMap<String, TreeMap<String, VariableState>> preStates = new TreeMap<>();
//    static TreeMap<String, TreeMap<String, VariableState>> postStates = new TreeMap<>();

    static Queue<String> worklist = new PriorityQueue<>();
    static Map<String, Set<String>> reachableTypesMap = new HashMap<>();
    // Soln for all instructions
    static Map<String, Set<ProgramPoint.Instruction>> reachingDefinitions = new TreeMap<>();

    public static void reachingDefinitionAnalysis(String filePath, String functionName) {
        parseLirFile(filePath, functionName);
        for (String type : typeDefinitions.keySet()) {
            Set<String> reachableTypes = calculateReachableTypes(type);
            reachableTypesMap.put(type, reachableTypes);
        }

        for (String blockName : blockVars.keySet()) {
            TreeMap<String, VariableState> initialStates = new TreeMap<>();
            preStates.put(blockName, initialStates);
        }

        for (String blockName : blockVars.keySet()) {
            TreeMap<String, VariableState> initialStates = new TreeMap<>();
            Set<String> varsInBlock = blockVars.get(blockName);
            for (String varName : varsInBlock) {
                VariableState newState = variableStates.get(varName).clone();
                initialStates.put(varName, newState);
            }

            for(String globalVar : globalVars){
                VariableState newState = new VariableState();
                initialStates.put(globalVar, newState);
            }
            preStates.put(blockName, initialStates);
        }

        TreeMap<String, VariableState> entryStates = preStates.get("entry");
        for (String param : localParams) {
            VariableState newState = variableStates.get(param).clone();
            entryStates.put(param, newState);
        }

        //Initial State ⊥ for all program points
        initializeVarsDefinitions();
        //Fake Heap Variables
        //Add fake heap variables to addressTakenVariables based on the analysis of pointer types (PTRSτ)

        worklist.add("entry");
        processedBlocks.add("entry");

        while (!worklist.isEmpty()) {
            String block = worklist.poll();
            TreeMap<String, VariableState> currentState = preStates.get(block);
            currentState = analyzeBlock(block, currentState, processedBlocks);

            for (String successor : blockSuccessors.getOrDefault(block, new LinkedList<>())) {
                TreeMap<String, VariableState> successorPreState = preStates.get(successor);
                TreeMap<String, VariableState> joinedState = joinMaps(successorPreState, currentState);
                if (!joinedState.equals(successorPreState) || currentState.isEmpty()) {
                    preStates.put(successor, joinedState);
                    if (!worklist.contains(successor)) {
                        processedBlocks.add(successor);
                        worklist.add(successor);
//                        System.out.println("Add to Worklist: " + worklist.toString());
                    }
                }
                if (!processedBlocks.contains(successor)) {
                    processedBlocks.add(successor);
                    worklist.add(successor);
                }
            }
        }
        printAnalysisResults();
    }

    private static TreeMap<String, VariableState> analyzeBlock(String block, TreeMap<String, VariableState> preState, Set<String> processedBlocks) {
        for (ProgramPoint.Instruction operation : basicBlocksInstructions.get(block)) {
            analyzeInstruction(preState, processedBlocks ,operation);
        }
        return preState;
    }

    private static TreeMap<String, VariableState> joinMaps(TreeMap<String, VariableState> map1, TreeMap<String, VariableState> map2) {
        TreeMap<String, VariableState> result = new TreeMap<>(map1);

        for (Map.Entry<String, VariableState> entry : map2.entrySet()) {
            String varName = entry.getKey();
            VariableState stateFromMap2 = entry.getValue();
            if (result.containsKey(varName)) {
                VariableState stateFromMap1 = result.get(varName);
                VariableState mergedState = stateFromMap1.join(stateFromMap2);
                result.put(varName, mergedState);
//                System.out.println("Merging state for variable '" + varName + "': " + stateFromMap1 + " ⊔ " + stateFromMap2 + " = " + mergedState);
            } else {
                result.put(varName, stateFromMap2);
//                System.out.println("Adding new state for variable '" + varName + "': " + stateFromMap2);
            }
        }

        return result;
    }

    private static void initializeVarsDefinitions(){
        TreeMap<String, VariableState> entryStates = preStates.get("entry");
        //alloc fake heap vars
        for (Map.Entry<String, VariableState> entry : fakeHeapStates.entrySet()) {
            String fakeVarName = entry.getKey();
            String type = entry.getValue().getType();
            Set<String> reachableTypes = calculateReachableTypes(fakeVarName);
            entryStates.put(fakeVarName, entry.getValue());
            allAddressTakenVars.add(fakeVarName);
            addressTakenVariables.computeIfAbsent(type, k -> new HashSet<>()).add(fakeVarName);
        }
    }

    static Set<String> calculateReachableTypes(String type) {
        Set<String> reachableTypes = new HashSet<>();
        if (!type.contains("->")) {
            reachableTypes.add(type);
        }

        if (typeDefinitions.containsKey(type)) {
            for (String fieldType : typeDefinitions.get(type)) {
                reachableTypes.addAll(calculateReachableTypes(fieldType));
            }
        } else if (type.startsWith("&")) {
            String pointedType = type.substring(1);
            reachableTypes.addAll(calculateReachableTypes(pointedType));
        }

        return reachableTypes;
    }


    private static void analyzeInstruction(TreeMap<String, VariableState> postState, Set<String> processedBlocks, ProgramPoint.Instruction input) {
        String instruction = input.getInstructure();
        Pattern operationPattern = Pattern.compile("\\$(store|load|alloc|cmp|gep|copy|call_ext|addrof|arith|gfp|ret|call_dir|call_idr|jump|branch)");
        Matcher matcher = operationPattern.matcher(instruction);
        String[] parts = instruction.split(" ");
        String defVar = parts[0];
        VariableState defState = postState.get(defVar);
        if (matcher.find()) {
            String opera = matcher.group(1);
            switch (opera) {
                case "store":
                    String useVar = parts[1];
                    String valueVar = parts[2];
                    String typeOfvalueVar = "int";
                    if(postState.get(valueVar) != null){
                        typeOfvalueVar = postState.get(valueVar).getType();
                    }
                    VariableState useState = postState.get(useVar);
                    VariableState valueState = postState.get(valueVar);
                    //∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    if (useState!= null) {
                        reachingDefinitions.get(input.toString()).addAll(useState.getDefinitionPoints());
                    }
                    if (valueState!= null) {
                        reachingDefinitions.get(input.toString()).addAll(valueState.getDefinitionPoints());
                    }

                    //  ∀x∈DEF,σ[x] ← σ[x] ∪ {pp}
                    if(addressTakenVariables.get(typeOfvalueVar) != null) {
                        for (String addTaken : addressTakenVariables.get(typeOfvalueVar)) {
                            if (postState.containsKey(addTaken)) {
                                postState.get(addTaken).addDefinitionPoint(input);
                            }
                        }
                    }
                    break;
                case "load":
//                    x marks all address-taken variables as potentially depending on this instruction.
                    String loadVar = parts[3];
                    VariableState loadState = postState.get(loadVar);
                    if(loadState != null) {
                        reachingDefinitions.get(input.toString()).addAll(loadState.definitionPoints);
                    }
                    //∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    if(defState.getType() != null && addressTakenVariables.get(defState.getType()) != null) {
                        for (String addTaken : addressTakenVariables.get(defState.getType())) {
                            reachingDefinitions.get(input.toString()).addAll(postState.get(addTaken).getDefinitionPoints());
                        }
                    }
                    // σ[x] ← {pp}
                    if(defState != null){
                        defState.setDefinitionPoint(input);
                    }
                    break;
                case "alloc":
                    String usedVar0 = parts[3];
                    VariableState usedState0 = postState.get(usedVar0);
                    if(usedState0 == null) {
                        usedVar0 = "fake_int";
                        usedState0 = postState.get(usedVar0);
                    }

                    //soln[pp] ← soln[pp] ∪ σ[v]
                    if (usedState0 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState0.getDefinitionPoints());
                    }
                    //σ[x] ← {pp}
                    defState.setDefinitionPoint(input);
                    break;
                case "cmp":
                    String usedVar3 = parts[4];
                    String usedVar4 = parts[5];
                    VariableState usedState3 = postState.get(usedVar3);
                    VariableState usedState4 = postState.get(usedVar4);
                    //soln[pp] ← soln[pp] ∪ σ[v]
                    if (usedState3 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState3.getDefinitionPoints());
                    }
                    if (usedState4 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState4.getDefinitionPoints());
                    }
                    //σ[x] ← {pp}
                    defState.setDefinitionPoint(input);
//                    handleCmp(parts, leftVar, postState);
                    break;
                case "arith":
                    String usedVar1 = parts[4];
                    String usedVar2 = parts[5];
                    VariableState usedState1 = postState.get(usedVar1);
                    VariableState usedState2 = postState.get(usedVar2);
                    //soln[pp] ← soln[pp] ∪ σ[v]
                    if (usedState1 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState1.getDefinitionPoints());
                    }
                    if (usedState2 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState2.getDefinitionPoints());
                    }
                    //σ[x] ← {pp}
                    defState.setDefinitionPoint(input);
//                    handleArith(parts, leftVar, postState);
                    break;
                case "gep":
                    String gepVar1 = parts[3];
                    String gepVar2 = parts[4];
                    VariableState gepState1 = postState.get(gepVar1);
                    VariableState gepState2 = postState.get(gepVar2);
                    //soln[pp] ← soln[pp] ∪ σ[v]
                    if (gepState1 != null) {
                        reachingDefinitions.get(input.toString()).addAll(gepState1.getDefinitionPoints());
                    }
                    if (gepState2 != null) {
                        reachingDefinitions.get(input.toString()).addAll(gepState2.getDefinitionPoints());
                    }
                    if(defState != null) {
                        reachingDefinitions.get(input.toString()).addAll(defState.getDefinitionPoints());
                    }
                    //σ[x] ← {pp}
                    defState.setDefinitionPoint(input);
                    break;
                case "gfp":
                //∀v∈USE,soln[pp]←soln[pp]∪σ[v] • σ[x] ← {pp}
                    String gfpVar1 = parts[3];
                    String gfpVar2 = parts[4];
                    VariableState gfpState1 = postState.get(gfpVar1);
                    VariableState gfpState2 = postState.get(gfpVar2);
                    //soln[pp] ← soln[pp] ∪ σ[v]
                    if (gfpState1 != null) {
                        reachingDefinitions.get(input.toString()).addAll(gfpState1.getDefinitionPoints());
                    }
                    if (gfpState2 != null) {
                        reachingDefinitions.get(input.toString()).addAll(gfpState2.getDefinitionPoints());
                    }
                    if(defState != null) {
                        reachingDefinitions.get(input.toString()).addAll(defState.getDefinitionPoints());
                    }
                    //σ[x] ← {pp}
                    defState.setDefinitionPoint(input);
                    break;
                case "copy":
                    if (parts.length > 3) {
                        String usedVar = parts[3];
                        VariableState usedState = postState.get(usedVar);
                        if(usedState != null) {
                            //soln[pp] ← soln[pp] ∪ σ[v]
                            Set<ProgramPoint.Instruction> set = reachingDefinitions.get(input.toString());
                            set.addAll(usedState.definitionPoints);
                        }
                        if(defState != null){
                            defState.setDefinitionPoint(input);
                            postState.put(defVar, defState);
                        }
                    }
                    break;
                case "call_ext":
                    // ∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    String varFnName1 = null;
                    if(instruction.contains("(") && instruction.contains(")")){
                        Pattern patternFn = Pattern.compile("(\\w+)\\((.*?)\\)");
                        Matcher matcherFn = patternFn.matcher(instruction);

                        if (matcherFn.find()) {
                            varFnName1 = matcherFn.group(1); // Function name
                            String functionArgs = matcherFn.group(2); // All arguments

                            VariableState fnState = postState.get(varFnName1);
                            if(fnState != null) {
                                reachingDefinitions.get(input.toString()).addAll(fnState.getDefinitionPoints());
                                fnState.addDefinitionPoint(input);
                            }

                            if (!functionArgs.isEmpty()) {
                                String[] args = functionArgs.split("\\s*,\\s*");
                                for(String arg : args){
                                    VariableState argState = postState.get(arg);
                                    if(argState!=null) {
                                        reachingDefinitions.get(input.toString()).addAll(argState.getDefinitionPoints());
                                        if(fnState != null) {
                                            argState.addDefinitionPoint(input);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // WDEF =[{addr_taken[τ]|τ ∈ ReachViaArgs ∪ ReachViaGlobals} ∪ Globals.
                    if(fnVarTypes.size() != 0) {
                        Set<String> typeSet3 = new HashSet<>();
                        for (String type3 : fnVarTypes.keySet()) {
                            if(reachableTypesMap.get(type3) != null) {
                                typeSet3.addAll(reachableTypesMap.get(type3));
                            }
                        }
                        for (String setType : typeSet3) {
                            for (String addTaken : addressTakenVariables.get(setType)) {
                                if (postState.containsKey(addTaken)) {
                                    postState.get(addTaken).addDefinitionPoint(input);
                                }
                            }
                        }
                    }
                    for(String globalVar : globalVars){
                        if (postState.containsKey(globalVar) && !globalVar.equals(varFnName1)) {
                            VariableState globalState = postState.get(globalVar);
                            reachingDefinitions.get(input.toString()).addAll(globalState.getDefinitionPoints());
                            globalState.addDefinitionPoint(input);
                        }
                    }
                    if(defState != null) {
                        defState.setDefinitionPoint(input);
                    }
                    break;
                case "call_dir":
//                    ∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    String varFnName2 = null;
                    if(instruction.contains("(") && instruction.contains(")")){
                        Pattern patternFn = Pattern.compile("(\\w+)\\((.*?)\\)");
                        Matcher matcherFn = patternFn.matcher(instruction);

                        if (matcherFn.find()) {
                            varFnName2 = matcherFn.group(1); // Function name
                            String functionArgs = matcherFn.group(2); // All arguments

                            VariableState fnState = postState.get(varFnName2);
                            if(fnState != null) {
                                reachingDefinitions.get(input.toString()).addAll(fnState.getDefinitionPoints());
                                fnState.addDefinitionPoint(input);
                            }

                            if (!functionArgs.isEmpty()) {
                                String[] args = functionArgs.split("\\s*,\\s*");
                                for(String arg : args){
                                    VariableState argState = postState.get(arg);
                                    if(argState!=null) {
                                        reachingDefinitions.get(input.toString()).addAll(argState.getDefinitionPoints());
                                        if(fnState != null) {
                                            argState.addDefinitionPoint(input);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // WDEF =[{addr_taken[τ]|τ ∈ ReachViaArgs ∪ ReachViaGlobals} ∪ Globals.
                    if(fnVarTypes.size() != 0) {
                        Set<String> typeSet2 = new HashSet<>();
                        for (String type2 : fnVarTypes.keySet()) {
                            if(reachableTypesMap.get(type2)!=null) {
                                typeSet2.addAll(reachableTypesMap.get(type2));
                            }
                        }
                        for (String type : typeSet2) {
                            for (String addTaken : addressTakenVariables.get(type)) {
                                if (postState.containsKey(addTaken)) {
                                    postState.get(addTaken).addDefinitionPoint(input);
                                }
                            }
                        }
                    }
                    for(String globalVar : globalVars){
                        if (postState.containsKey(globalVar) && !globalVar.equals(varFnName2)) {
                            VariableState globalState = postState.get(globalVar);
                            reachingDefinitions.get(input.toString()).addAll(globalState.getDefinitionPoints());
                            globalState.addDefinitionPoint(input);
                        }
                    }
                    if(defState != null){
                        defState.setDefinitionPoint(input);
                    }
                    break;
                case "call_idr":
                    // ∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    String varFnName3 = null;
                    if(instruction.contains("(") && instruction.contains(")")){
                        Pattern patternFn = Pattern.compile("(\\w+)\\((.*?)\\)");
                        Matcher matcherFn = patternFn.matcher(instruction);

                        if (matcherFn.find()) {
                            varFnName3 = matcherFn.group(1); // Function name
                            String functionArgs = matcherFn.group(2); // All arguments

                            VariableState fnState = postState.get(varFnName3);
                            if(fnState != null) {
                                reachingDefinitions.get(input.toString()).addAll(fnState.getDefinitionPoints());
                                fnState.addDefinitionPoint(input);
                            }

                            if (!functionArgs.isEmpty()) {
                                String[] args = functionArgs.split("\\s*,\\s*");
                                for(String arg : args){
                                    VariableState argState = postState.get(arg);
                                    if(argState!=null) {
                                        reachingDefinitions.get(input.toString()).addAll(argState.getDefinitionPoints());
                                        argState.addDefinitionPoint(input);
                                    }
                                }
                            }
                        }
                    }
                    // WDEF =[{addr_taken[τ]|τ ∈ ReachViaArgs ∪ ReachViaGlobals} ∪ Globals.
                    if(fnVarTypes.size() != 0) {
                        Set<String> typeSet3 = new HashSet<>();
                        for (String type3 : fnVarTypes.keySet()) {
                            if(reachableTypesMap.get(type3)!=null) {
                                typeSet3.addAll(reachableTypesMap.get(type3));
                            }
                        }
                        for (String setType : typeSet3) {
                            for (String addTaken : addressTakenVariables.get(setType)) {
                                if (postState.containsKey(addTaken)) {
                                    postState.get(addTaken).addDefinitionPoint(input);
                                }
                            }
                        }
                    }
                    for(String globalVar : globalVars){
                        if (postState.containsKey(globalVar) && !globalVar.equals(varFnName3)) {
                            VariableState globalState = postState.get(globalVar);
                            reachingDefinitions.get(input.toString()).addAll(globalState.getDefinitionPoints());
                            globalState.addDefinitionPoint(input);
                        }
                    }
                    if(defState != null) {
                        defState.setDefinitionPoint(input);
                    }
                    break;
                case "addrof":
                    if (parts.length > 2) {
                        Set<ProgramPoint.Instruction> set3 = reachingDefinitions.get(input.toString());
                        set3.addAll(defState.definitionPoints);
                        defState.setDefinitionPoint(input);
                    }
                    break;
                case "jump":
                    String targetBlockJump = extractTargetBlock(instruction);
                    break;
                case "branch":
                    String usedVar5 = parts[1];
                    VariableState usedState5 = postState.get(usedVar5);
                    // branch maybe integer
                    //∀v∈USE,soln[pp] ← soln[pp] ∪ σ[v]
                    if(usedState5 != null) {
                        reachingDefinitions.get(input.toString()).addAll(usedState5.getDefinitionPoints());
                    }
                    break;
                case "ret":
                    if(parts.length>0) {
                        String retVar = parts[1];
                        // ret could return integer
                        VariableState retState = postState.get(retVar);
                        if(retState != null) {
                            reachingDefinitions.get(input.toString()).addAll(retState.getDefinitionPoints());
                        }
                    }
                    break;
                default:
                    break;
            }
        }
    }

    private static String getAddressTaken(VariableState pointerState, TreeMap<String, VariableState> postState){
        VariableState result = pointerState.clone();
        String re = "";
        while(result.pointsTo!=null){
            re = result.pointsTo;
            result = postState.get(result.pointsTo);
        }
        return re;
    }

    private static void parseLirFile(String filePath, String functionName) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String currentBlock = null;
            boolean isMainFunction = false;
            boolean isOtherFunction = false;
            boolean isStruct = false;
            String structName = "";
            int index = 0;

            String line;
            while ((line = reader.readLine()) != null) {
                line = line.trim();

                if(line.length() == 0) continue;
                if (line.startsWith("fn "+functionName)) {
                    isMainFunction = true;
                    if(line.contains(":") && line.contains("(")) {
                        String paramSubstring = line.substring(line.indexOf('(') + 1, line.indexOf(')'));
                        StringBuilder transformedPart = new StringBuilder();
                        int parenthesisLevel = 0;
                        for (char c : paramSubstring.toCharArray()) {
                            if (c == '(') {
                                parenthesisLevel++;
                            }else if (c == ')'){
                                parenthesisLevel--;
                            } else if (c == ',' && parenthesisLevel > 0){
                                c = '|';
                            }
                            transformedPart.append(c);
                        }
                        String[] variables = paramSubstring.split(",\\s*");
                        for (String varDeclaration : variables) {
                            String[] parts = varDeclaration.split(":");
                            String varName = parts[0].trim();
                            // just get int type
                            String type = parts[1].trim();
                            VariableState newState = new VariableState();
                            newState.setType(type);
                            if (type.startsWith("&")) {
                                newState.setPointsTo(type.substring(1));
                            }
                            localParams.add(varName);
                            variableStates.put(varName, newState);
                        }
                    }
                } else if (line.startsWith("fn ") && !line.contains(functionName)) {
                    isOtherFunction = true;
                    String fnName = null;
                    Pattern pattern = Pattern.compile("fn (\\w+)\\s*\\(");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        fnName = matcher.group(1);
                    }
                    if(line.contains(":") && line.contains("(")) {
                        String paramSubstring = line.substring(line.indexOf('(') + 1, line.indexOf(')'));
                        StringBuilder transformedPart = new StringBuilder();
                        int parenthesisLevel = 0;
                        for (char c : paramSubstring.toCharArray()) {
                            if (c == '(') {
                                parenthesisLevel++;
                            }else if (c == ')'){
                                parenthesisLevel--;
                            } else if (c == ',' && parenthesisLevel > 0){
                                c = '|';
                            }
                            transformedPart.append(c);
                        }
                        fnVarTypes.putIfAbsent(fnName, new HashSet<>());
                        String[] variables = paramSubstring.split(",\\s*");
                        for (String varDeclaration : variables) {
                            String[] parts = varDeclaration.split(":");
                            String type = parts[1].trim();
                            fnVarTypes.computeIfAbsent(fnName, k -> new HashSet<>()).add(type);
                            if(type.contains("&")){
                                VariableState fakeState = new VariableState();
                                fakeState.setType(type);
                                fakeHeapStates.putIfAbsent("fake_" + fakeState.getType(), fakeState);
                            }
                        }
                    }
                }else if (isOtherFunction && line.startsWith("}")) {
                    isOtherFunction = false;
                    currentBlock = null;
                } else if (isMainFunction && line.startsWith("}")) {
                    isMainFunction = false;
                    currentBlock = null;
                } else if(line.startsWith("struct ")){
                    isStruct = true;
                    Pattern pattern = Pattern.compile("struct\\s+(\\w+)\\s*\\{");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        structName = matcher.group(1);
                    }
                } else if(isStruct && line.startsWith("}")) {
                    isStruct = false;
                } else if(isStruct){
                    Pattern fieldPattern = Pattern.compile("\\s*(\\w+):\\s*(.+);");
                    Matcher fieldMatcher = fieldPattern.matcher(line);
                    if (fieldMatcher.find()) {
                        String fieldName = fieldMatcher.group(1);
                        String fieldType = fieldMatcher.group(2);
                    }
                }else if (!isMainFunction && !isOtherFunction && !isStruct && line.matches("^\\w+:.*$")) {
                    Pattern pattern = Pattern.compile("^(\\w+):.*$");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        String varName = matcher.group(1);
                        globalVars.add(varName);
//                        VariableState fakeState = new VariableState();
//                        fakeState.setType("int");
//                        fakeHeapStates.putIfAbsent("fake_" + fakeState.getType(), fakeState);
                    }
                } else if (isMainFunction) {
                    if (line.matches("^\\w+:")) {
                        //There is a new block
                        currentBlock = line.replace(":", "");
                        blockVars.putIfAbsent(currentBlock, new HashSet<>());
                        basicBlocksInstructions.putIfAbsent(currentBlock, new ArrayList<>());
                        index = 0;
                    } else {
                        if (line.startsWith("let ")) {
                            String variablesPart = line.substring("let ".length());
                            StringBuilder transformedPart = new StringBuilder();
                            int parenthesisLevel = 0;
                            for (char c : variablesPart.toCharArray()) {
                                if (c == '(') {
                                    parenthesisLevel++;
                                } else if (c == ')') {
                                    parenthesisLevel--;
                                } else if (c == ',' && parenthesisLevel > 0) {
                                    c = '|';
                                }
                                transformedPart.append(c);
                            }
                            String[] variables = transformedPart.toString().split(",\\s*");
                            for (String varDeclaration : variables) {
                                String[] parts = varDeclaration.split(":");
                                String varName = parts[0].trim();
                                // just get int type
                                String type = parts[1].trim();
                                VariableState newState = new VariableState();
                                newState.setType(type);
                                if (type.startsWith("&")) {
                                    newState.setPointsTo(type.substring(1));
                                }
                                variableStates.put(varName, newState);
                            }
                        } else if (line.contains("$addrof")) {
                            ProgramPoint.NonTermInstruction instruction = new ProgramPoint.NonTermInstruction(currentBlock, index, line);
                            index++;
                            basicBlocksInstructions.get(currentBlock).add(instruction);
                            reachingDefinitions.put(instruction.toString(), new HashSet<>());
                            String[] parts = line.split(" ");
                            Set<String> varsInBlock = blockVars.get(currentBlock);
                            for (int i = 0; i < parts.length; i++) {
                                String part = parts[i];
                                if (variableStates.containsKey(part)) {
                                    varsInBlock.add(part);
                                }
                            }
                            if (parts.length > 3) {
                                String address = parts[0];
                                String addressTakenVar = parts[3];
                                VariableState varState = variableStates.get(address);
                                varState.setPointsTo(addressTakenVar);
                                if (variableStates.containsKey(addressTakenVar)) {
                                    String type = variableStates.get(addressTakenVar).getType();
                                    allAddressTakenVars.add(addressTakenVar);
                                    addressTakenVariables.computeIfAbsent(type, k -> new HashSet<>()).add(addressTakenVar);
                                }
                            }
                        } else {
                            ProgramPoint.Instruction instruction;
                            Set<String> varsInBlock = blockVars.get(currentBlock);
                            String[] parts = line.split(" ");
                            for (int i = 0; i < parts.length; i++) {
                                String part = parts[i];
                                if (variableStates.containsKey(part)) {
                                    VariableState thisVar = variableStates.get(part);
                                    varsInBlock.add(part);
                                }
                            }
                            if(line.contains("alloc")){
                                if(variableStates.get(parts[3]) == null) {
                                    VariableState fakeState = new VariableState();
                                    fakeState.setType("int");
                                    fakeHeapStates.put("fake_" + fakeState.getType(), fakeState);
                                    variableStates.get(parts[0]).setPointsTo("fake_" + fakeState.getType());
                                }
                            }
                            if (currentBlock != null) {
                                if (line.startsWith("$jump")) {
                                    instruction = new ProgramPoint.Terminal(currentBlock, line);
                                    String targetBlock = extractTargetBlock(line);
                                    blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                                } else if (line.startsWith("$branch")) {
                                    instruction = new ProgramPoint.Terminal(currentBlock, line);
                                    blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[2]); // trueBlock
                                    blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[3]); // falseBlock
                                } else if (line.contains("then")) {
                                    instruction = new ProgramPoint.Terminal(currentBlock, line);
                                    String targetBlock = line.substring(line.lastIndexOf("then") + 5).trim();
                                    blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                                } else if (line.contains("ret")) {
                                    instruction = new ProgramPoint.Terminal(currentBlock, line);
                                } else {
                                    instruction = new ProgramPoint.NonTermInstruction(currentBlock, index, line);
                                    index++;
                                }
                                basicBlocksInstructions.get(currentBlock).add(instruction);
                                reachingDefinitions.put(instruction.toString(), new HashSet<>());
                            } else {

                            }
                        }
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static String extractTargetBlock(String instruction) {
        Pattern pattern = Pattern.compile("\\$(branch|jump)\\s+(\\w+)");
        Matcher matcher = pattern.matcher(instruction);
        if (matcher.find()) {
            return matcher.group(2);
        }
        return "";
    }

    private static void printAnalysisResults() {
        // Sort the basic block names alphabetically
        for (Map.Entry<String, Set<ProgramPoint.Instruction>> entry : reachingDefinitions.entrySet()) {
            String instruction = entry.getKey();
            Set<ProgramPoint.Instruction> definitions = entry.getValue();

            // Skip this entry if definitions set is empty
            if (definitions.isEmpty()) {
                continue;
            }

            StringBuilder result = new StringBuilder(instruction.toString() + " -> {");

            List<String> defsStrings = definitions.stream()
                    .map(Object::toString)
                    .sorted()
                    .collect(Collectors.toList());

            result.append(String.join(", ", defsStrings));
            result.append("}");

            System.out.println(result.toString());
        }
    }

    public static void main(String[] args) {
        if (args.length < 2) {
            System.out.println("Usage: java DataFlowConstants <lir_file_path> <json_file_path> <function_name>");
            System.exit(1);
        }
        String lirFilePath = args[0];
        String functionName = "test";
        if(args.length > 2 && args[2].length()!=0){
            functionName = args[2];
        }
        reachingDefinitionAnalysis(lirFilePath, functionName);
    }
}