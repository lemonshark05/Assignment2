import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class DataFlowRdef {

    static Map<String, VariableState> addressTakenVarInit = new TreeMap<>();
    static Map<String, Set<String>> addressTakenVariables = new TreeMap<>();

    static Map<String, List<String>> typeDefinitions = new HashMap<>();
    static Set<String> allVars = new HashSet<>();

    static Set<String> globalIntVars = new HashSet<>();
    static Set<String> localIntParams = new HashSet<>();

    static Map<ProgramPoint.Instruction, List<ProgramPoint.Instruction>> instructionSuccessors = new HashMap<>();

    static Map<String, List<ProgramPoint.Instruction>> basicBlocksInstructions = new HashMap<>();

    static Map<String, List<String>> blockSuccessors = new HashMap<>();

    static Map<String, TreeMap<String, String>> blockVars = new HashMap<>();
    static Map<String, VariableState> variableStates = new TreeMap<>();
    static Set<String> processedBlocks = new HashSet<>();

    static Queue<ProgramPoint.Instruction> worklist = new PriorityQueue<>();
    static Map<ProgramPoint.Instruction, Set<ProgramPoint.Instruction>> reachingDefinitions = new TreeMap<>();

    public static void reachingDefinitions(String filePath, String functionName) {
        parseLirFile(filePath, functionName);
        //Initial State ⊥ for all program points
        initializeVarsDefinitions();
        //Fake Heap Variables
        //Add fake heap variables to addressTakenVariables based on the analysis of pointer types (PTRSτ)

        ProgramPoint.Instruction entryBlock = getFirstInstructionOfBlock("entry");
        worklist.add(entryBlock);
        processedBlocks.add("entry");

        while (!worklist.isEmpty()) {
            ProgramPoint.Instruction currentInstruction = worklist.poll();
            Set<ProgramPoint.Instruction> currentDefs = reachingDefinitions.get(currentInstruction);
            Set<ProgramPoint.Instruction> updatedDefs = analyzeInstruction(currentInstruction, currentDefs);

            if (!currentDefs.equals(updatedDefs)) {
                reachingDefinitions.put(currentInstruction, updatedDefs);
                for (ProgramPoint.Instruction successor : currentInstruction.getSuccessors()) {
                    if (!worklist.contains(successor)) {
                        worklist.add(successor);
                    }
                }
            }
        }
        printAnalysisResults();
    }

    public static ProgramPoint.Instruction getFirstInstructionOfBlock(String blockName) {
        List<ProgramPoint.Instruction> instructions = basicBlocksInstructions.get(blockName);

        if (instructions != null && !instructions.isEmpty()) {
            return instructions.get(0);
        }
        return null;
    }

    void addSuccessorsToWorklist(ProgramPoint.Instruction instruction) {
        List<ProgramPoint.Instruction> successors = instructionSuccessors.get(instruction);
        if (successors != null) {
            for (ProgramPoint.Instruction succ : successors) {
                if (!worklist.contains(succ)) {
                    worklist.add(succ);
                }
            }
        }
    }

    private static void initializeVarsDefinitions(){
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


    private static Set<ProgramPoint.Instruction> analyzeInstruction(ProgramPoint.Instruction input, Set<ProgramPoint.Instruction> currentDefs) {
        Set<ProgramPoint.Instruction> updatedDefs = new HashSet<>(currentDefs);
        String instruction = input.getInstructure();
        Pattern operationPattern = Pattern.compile("\\$(store|load|alloc|cmp|gep|copy|call_ext|addrof|arith|gfp|ret|call_dir|call_idr|jump|branch)");
        Matcher matcher = operationPattern.matcher(instruction);
        String[] parts = instruction.split(" ");
        String leftVar = parts[0];
        if (matcher.find()) {
            String opera = matcher.group(1);
            switch (opera) {
                case "store":
                    String pointerVar = parts[1];
                    String valueVar = parts[2];
                    if (valueVar.matches("\\d+")) {
                        int contant = Integer.parseInt(valueVar);
                        for(String addVar : addressTakenVarInit.keySet()){
                            VariableState newState = new VariableState();
                            newState.setInt(true);
                            newState.setConstantValue(contant);
                        }
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
                    if (parts.length > 3) {
                        String copiedVar = parts[3];
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
                        String pointedVar = parts[3];
                        variableStates.get(leftVar).setPointsTo(pointedVar);
                    }
                    break;
                case "gfp":

                    break;
                case "jump":
                    String targetBlockJump = extractTargetBlock(instruction);
                    break;
                case "branch":
                    String condition = parts[1];
                    String trueTarget = parts[2];
                    String falseTarget = parts[3];
                    List<String> newSuccessor = new ArrayList<>();
                    break;
                case "ret":
                    break;
                default:
                    break;
            }
        }
        return updatedDefs;
    }

    private static String getAbstractValue(String operand, Map<String, VariableState> postStates) {
        VariableState state =new VariableState();
        try {
            int value = Integer.parseInt(operand);
            return value+"";
        } catch (NumberFormatException e) {
            // Not an integer, so it should be a variable name
            if(postStates.containsKey(operand)) {
                state = postStates.get(operand);
            }else{
                state = variableStates.get(operand);
            }
            if(state.isTop){
                return "T";
            }else if(state.hasConstantValue()){
                int stateValue = state.getConstantValue();
                return stateValue+"";
            }else if(state.isBottom()){
                return "B";
            }else if(state.pointsTo != null){
                return "T";
            }
        }
        return "";
    }

    private static void handleArith(String[] parts, String leftVar, Map<String, VariableState> postStates) {
        if (parts.length < 5) return;

        if(leftVar.equals("_t7")){
            String a = leftVar;
        }

        VariableState leftState = postStates.get(leftVar);
        String operation = parts[3];
        String operand1 = parts[4];
        String operand2 = parts[5];

        String state1 = getAbstractValue(operand1, postStates);
        String state2 = getAbstractValue(operand2, postStates);

        if (state1.equals("B") || state2.equals("B")){
            leftState.markAsBottom();
            return;
        }

        if(operation.equals("mul")){
            if(state1.equals("0") || state2.equals("0")){
                leftState.setConstantValue(0);
                return;
            }
        }

        if(operation.equals("div")){
            if(state2.equals("0")){
                leftState.markAsBottom();
                return;
            }else if(state1.equals("0")){
                leftState.setConstantValue(0);
                return;
            }
        }

        if (state1.equals("T") || state2.equals("T")) {
            leftState.markAsTop();
            return;
        }

        try {
            Integer value1 = Integer.parseInt(state1);
            Integer value2 = Integer.parseInt(state2);
            if (value1 != null && value2 != null) {
                Integer result = performArithmetic(operation, value1, value2);
                if (result != null) {
                    leftState.setConstantValue(result);
                } else {
                    leftState.markAsBottom();
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static void handleCmp(String[] parts, String leftVar, Map<String, VariableState> postStates) {
        if (parts.length < 5) return;

        if(leftVar.equals("_t14")){
            String a = leftVar;
        }

        VariableState leftState = postStates.get(leftVar);
        String operation = parts[3];
        String operand1 = parts[4];
        String operand2 = parts[5];

        String state1 = getAbstractValue(operand1, postStates);
        String state2 = getAbstractValue(operand2, postStates);

        if (state1.equals(state2) && state1.equals("B")) {
            leftState.markAsBottom();
            return;
        }else if(state1.equals(state2) && state1.equals("T")){
            leftState.markAsTop();
            return;
        }else if(state1.length() == 0){
            leftState.markAsBottom();
            return;
        }else if (state1.equals("B") || state2.equals("B")){
            leftState.markAsBottom();
            return;
        }else if (state1.equals("T") || state2.equals("T")) {
            leftState.markAsTop();
            return;
        }

        try {
            Integer value1 = Integer.parseInt(state1);
            Integer value2 = Integer.parseInt(state2);
            boolean result = performComparison(operation, value1, value2);
            if(!result){
                leftState.setConstantValue(0);
            }else{
                leftState.setConstantValue(1);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static void parseLirFile(String filePath, String functionName) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String currentBlock = null;
            boolean isFunction = false;
            boolean isStruct = false;
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
                            if (type.startsWith("&int")) {
                                newState.setPointsTo(type.substring(1));
                            } else if (type.equals("int")) {
                                newState.setInt(true);
                            } else if (type.startsWith("&")) {
                                newState.setPointsTo(type.substring(1));
                            }
                            newState.markAsTop();
                            localIntParams.add(varName);
                            allVars.add(varName);
                            variableStates.put(varName, newState);
                        }
                    }
                } else if (isFunction && line.startsWith("}")) {
                    isFunction = false;
                    currentBlock = null;
                } else if(line.startsWith("struct ")){
                    isStruct = true;
                } else if(isStruct && line.startsWith("}")) {
                    isStruct = false;
                } else if (!isFunction && !isStruct && line.matches("^\\w+:int$")) {
                    Pattern pattern = Pattern.compile("^(\\w+):int$");
                    Matcher matcher = pattern.matcher(line);
                    if (matcher.find()) {
                        String varName = matcher.group(1);
                        globalIntVars.add(varName);
                        allVars.add(varName);
                    }
                } else if (isFunction) {
                    if (line.matches("^\\w+:")) {
                        currentBlock = line.replace(":", "");
                        blockVars.putIfAbsent(currentBlock, new TreeMap<>());
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
                                newState.type = type;
                                if (type.startsWith("&int")) {
                                    newState.setPointsTo(type.substring(1));
                                } else if (type.equals("int")) {
                                    newState.setInt(true);
                                } else if (type.startsWith("&")) {
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
                            TreeMap<String, String> varsInBlock = blockVars.get(currentBlock);
                            for (int i = 0; i < parts.length; i++) {
                                String part = parts[i];
                                if (variableStates.containsKey(part) && variableStates.get(part).isInt()) {
                                    varsInBlock.put(part, "");
                                }
                            }
                            if (parts.length > 3) {
                                String address = parts[0];
                                String addressTakenVar = parts[3];
                                VariableState varState = variableStates.get(addressTakenVar);
                                varState.setPointsTo(addressTakenVar);
                                if (variableStates.containsKey(addressTakenVar)) {
                                    String type = varState.getType();
                                    addressTakenVariables.computeIfAbsent(type, k -> new HashSet<>()).add(addressTakenVar);
                                }
                            }
                        } else {
                            ProgramPoint.Instruction instruction;
                            TreeMap<String, String> varsInBlock = blockVars.get(currentBlock);
                            String[] parts = line.split(" ");
                            for (int i = 0; i < parts.length; i++) {
                                String part = parts[i];
                                if (variableStates.containsKey(part)) {
                                    VariableState thisVar = variableStates.get(part);
                                    if (thisVar.isInt()) {
                                        varsInBlock.put(part, "");
                                    }
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

    private static Integer performArithmetic(String op, Integer val1, Integer val2) {
        switch (op) {
            case "add":
                return val1 + val2;
            case "sub":
                return val1 - val2;
            case "mul":
                return val1 * val2;
            case "div":
                if (val2 == 0) return null;
                return val1 / val2;
            default:
                return null;
        }
    }
    private static Boolean performComparison(String op, Integer val1, Integer val2) {
        switch (op) {
            case "eq":
                return Objects.equals(val1, val2);
            case "neq":
                return !Objects.equals(val1, val2);
            case "lt":
                return val1 < val2;
            case "lte":
                return val1 <= val2;
            case "gt":
                return val1 > val2;
            case "gte":
                return val1 >= val2;
            default:
                return null;
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

    Comparator<ProgramPoint.Instruction> blockNameComparator = new Comparator<ProgramPoint.Instruction>() {
        @Override
        public int compare(ProgramPoint.Instruction o1, ProgramPoint.Instruction o2) {
            int result = o1.getBb().compareTo(o2.getBb());
            if (result == 0 && o1 instanceof ProgramPoint.NonTermInstruction && o2 instanceof ProgramPoint.NonTermInstruction) {
                return Integer.compare(((ProgramPoint.NonTermInstruction) o1).getIndex(), ((ProgramPoint.NonTermInstruction) o2).getIndex());
            } else if (o1 instanceof ProgramPoint.NonTermInstruction && o2 instanceof ProgramPoint.Terminal) {
                return -1;
            } else if (o1 instanceof ProgramPoint.Terminal && o2 instanceof ProgramPoint.NonTermInstruction) {
                return 1;
            }
            return result;
        }
    };

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