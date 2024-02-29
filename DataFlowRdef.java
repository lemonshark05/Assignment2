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
    static Set<String> allVars = new HashSet<>();

    static Set<String> globalVars = new HashSet<>();
    static Set<String> localParams = new HashSet<>();

    static Map<String, List<ProgramPoint.Instruction>> basicBlocksInstructions = new HashMap<>();

    static Map<String, List<String>> blockSuccessors = new HashMap<>();

    static Map<String, Set<String>> blockVars = new HashMap<>();
    static Map<String, VariableState> variableStates = new TreeMap<>();
    static Set<String> processedBlocks = new HashSet<>();

    static TreeMap<String, TreeMap<String, VariableState>> preStates = new TreeMap<>();
    static TreeMap<String, TreeMap<String, VariableState>> postStates = new TreeMap<>();

    static Queue<String> worklist = new PriorityQueue<>();
    static Map<String, Set<String>> reachableTypes = new HashMap<>();
    // Soln for all instructions
    static Map<ProgramPoint.Instruction, Set<ProgramPoint.Instruction>> reachingDefinitions = new TreeMap<>();

    public static void reachingDefinitions(String filePath, String functionName) {
        parseLirFile(filePath, functionName);
        for (String blockName : blockVars.keySet()) {
            TreeMap<String, VariableState> initialStates = new TreeMap<>();
            preStates.put(blockName, initialStates);
        }
        //Initial State ⊥ for all program points
        initializeVarsDefinitions();
        //Fake Heap Variables
        //Add fake heap variables to addressTakenVariables based on the analysis of pointer types (PTRSτ)
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

        worklist.add("entry");
        processedBlocks.add("entry");

        while (!worklist.isEmpty()) {
            String block = worklist.poll();
            TreeMap<String, VariableState> preState = preStates.get(block);
            TreeMap<String, VariableState> postState = analyzeBlock(block, preState, processedBlocks);
            postStates.put(block, postState);

            for (String successor : blockSuccessors.getOrDefault(block, new LinkedList<>())) {
                TreeMap<String, VariableState> successorPreState = preStates.get(successor);
                TreeMap<String, VariableState> joinedState = joinMaps(successorPreState, postState);
                if (!joinedState.equals(successorPreState) || postState.isEmpty()) {
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

    private static TreeMap<String, VariableState> analyzeBlock(String block, TreeMap<String, VariableState> pState, Set<String> processedBlocks) {
        TreeMap<String, VariableState> postState = new TreeMap<>();
        for (Map.Entry<String, VariableState> entry : pState.entrySet()) {
            VariableState newState = entry.getValue().clone();
            postState.put(entry.getKey(), newState);
        }
        for (ProgramPoint.Instruction operation : basicBlocksInstructions.get(block)) {
            analyzeInstruction(postState, processedBlocks ,operation);
        }
        return postState;
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
        //alloc fake heap vars
        Set<String> pointerTypes = new HashSet<>();

        for (String ptrType : pointerTypes) {
            Set<String> reachableTypes = calculateReachableTypes(ptrType);
            for (String type : reachableTypes) {
                String fakeVarName = "fake_" + type.replace("&", "").replace(" ", "_");
                addressTakenVariables.computeIfAbsent(type, k -> new HashSet<>()).add(fakeVarName);
            }
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
                    String pointerVar = parts[1];
                    String valueVar = parts[2];
                    if(defState != null){
                        defState.addDefinitionPoint(input);
                    }
                    if (valueVar.matches("\\d+")) {


                    }
                    VariableState variableState = variableStates.get(pointerVar);
//                    if (variableState.pointsTo != null) {
//                        Set<ProgramPoint.Instruction> defsOfValue = findDefinitionsOf(valueVar, currentDefs);
//                        for (String fakeVar : findFakeVariablesForPointerType(pointerVar)) {
//                            updatedDefs.addAll(defsOfValue);
//                        }
//                    }
                    break;
                case "load":

                    break;
                case "alloc":

                    break;
                case "cmp":
//                    handleCmp(parts, leftVar, postState);
                    break;
                case "arith":
//                    handleArith(parts, leftVar, postState);
                    break;
                case "gep":
                    break;
                case "copy":
                    if(defState != null){
                        defState.addDefinitionPoint(input);
                    }
                    if (parts.length > 3) {
                        String copiedVar = parts[3];
                        VariableState copiedState = postState.get(copiedVar);
                        if (copiedState != null) {
                            defState.addAllDefinitionPoint(copiedState.definitionPoints);
                            Set<ProgramPoint.Instruction> set = reachingDefinitions.get(input);
                            set.addAll(defState.definitionPoints);
                        } else {
                            try {
                                int value = Integer.parseInt(copiedVar);
                            } catch (NumberFormatException e) {

                            }
                        }
                    }
                    break;
                case "call_ext":
                    break;
                case "call_dir":
                    break;
                case "call_idr":
                    break;
                case "addrof":
                    if (parts.length > 2) {
                        defState.addDefinitionPoint(input);
                    }
                    break;
                case "gfp":

                    break;
                case "jump":
                    String targetBlockJump = extractTargetBlock(instruction);
                    break;
                case "branch":

                    break;
                case "ret":
                    break;
                default:
                    break;
            }
        }
    }

    private static void parseLirFile(String filePath, String functionName) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String currentBlock = null;
            boolean isFunction = false;
            boolean isStruct = false;
            String structName = "";
            int index = 0;

            String line;
            while ((line = reader.readLine()) != null) {
                line = line.trim();

                if(line.length() == 0) continue;
                if (line.startsWith("fn "+functionName)) {
                    isFunction = true;
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
                            allVars.add(varName);
                            variableStates.put(varName, newState);
                        }
                    }
                } else if (isFunction && line.startsWith("}")) {
                    isFunction = false;
                    currentBlock = null;
                } else if(line.startsWith("struct ")){
                    isStruct = true;
                    Pattern pattern = Pattern.compile("struct\\s+(\\w+)\\s*\\{");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        structName = matcher.group(1);
                    }
                    if (!reachableTypes.containsKey(structName)) {
                        reachableTypes.put(structName, new HashSet<>());
                    }
                } else if(isStruct && line.startsWith("}")) {
                    isStruct = false;
                } else if(isStruct){
                    Pattern fieldPattern = Pattern.compile("\\s*(\\w+):\\s*(.+);");
                    Matcher fieldMatcher = fieldPattern.matcher(line);
                    if (fieldMatcher.find()) {
                        String fieldName = fieldMatcher.group(1);
                        String fieldType = fieldMatcher.group(2);
                        reachableTypes.computeIfAbsent(structName, k -> new HashSet<>()).add(fieldType);
                    }
                }else if (!isFunction && !isStruct && line.matches("^\\w+:$")) {
                    Pattern pattern = Pattern.compile("^(\\w+):$");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        String varName = matcher.group(1);
                        globalVars.add(varName);
                        allVars.add(varName);
                    }
                } else if (isFunction) {
                    if (line.matches("^\\w+:")) {
                        currentBlock = line.replace(":", "");
                        blockVars.putIfAbsent(currentBlock, new HashSet<>());
                        basicBlocksInstructions.putIfAbsent(currentBlock, new ArrayList<>());
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
                                allVars.add(varName);
                                variableStates.put(varName, newState);
                            }
                        } else if (line.contains("$addrof")) {
                            ProgramPoint.NonTermInstruction instruction = new ProgramPoint.NonTermInstruction(currentBlock, index, line);
                            index++;
                            basicBlocksInstructions.get(currentBlock).add(instruction);
                            reachingDefinitions.put(instruction, new HashSet<>());
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
                                    instruction = new ProgramPoint.NonTermInstruction(currentBlock, index, line);
                                    index++;
                                    String targetBlock = line.substring(line.lastIndexOf("then") + 5).trim();
                                    blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                                } else if (line.contains("ret")) {
                                    instruction = new ProgramPoint.Terminal(currentBlock, line);
                                } else {
                                    instruction = new ProgramPoint.NonTermInstruction(currentBlock, index, line);
                                    index++;
                                }
                                basicBlocksInstructions.get(currentBlock).add(instruction);
                                reachingDefinitions.put(instruction, new HashSet<>());
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
        for (Map.Entry<ProgramPoint.Instruction, Set<ProgramPoint.Instruction>> entry : reachingDefinitions.entrySet()) {
            ProgramPoint.Instruction instruction = entry.getKey();
            Set<ProgramPoint.Instruction> definitions = entry.getValue();
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
        reachingDefinitions(lirFilePath, functionName);
    }
}