import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class DataFlowControl {

    static class Operation {
        String block;
        String instruction;

        Operation(String block, String instruction) {
            this.block = block;
            this.instruction = instruction;
        }
    }

    static Set<String> addressTakenVariables = new HashSet<>();
    static Map<String, VariableState> addressTakenVarInit = new TreeMap<>();
    static Set<String> allVars = new HashSet<>();

    static Set<String> globalIntVars = new HashSet<>();
    static Set<String> localIntParams = new HashSet<>();

    static TreeMap<String, List<Operation>> basicBlocks = new TreeMap<>();
    static TreeMap<String, List<String>> blockSuccessors = new TreeMap<>();

    static TreeMap<String, Set<String>> dominators = new TreeMap<>();
    static TreeMap<String, Set<String>> dominanceFrontiers = new TreeMap<>();

    static Map<String, TreeMap<String, String>> blockVars = new HashMap<>();
    static Map<String, VariableState> variableStates = new TreeMap<>();
    static Set<String> processedBlocks = new HashSet<>();

    static Queue<String> worklist = new PriorityQueue<>();

    static TreeMap<String, TreeMap<String, VariableState>> preStates = new TreeMap<>();
    static TreeMap<String, TreeMap<String, VariableState>> postStates = new TreeMap<>();


    public static void controlDominanceAnalysis(String filePath, String functionName) {
        parseLirFile(filePath, functionName);

        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<String, List<Operation>> entry : basicBlocks.entrySet()) {
                String block = entry.getKey();
                Set<String> newDominators = new HashSet<>(basicBlocks.keySet());
                for (String pred : getPredecessors(block)) {
                    newDominators.retainAll(dominators.get(pred));
                }
                newDominators.add(block); // A block always dominates itself
                if (!newDominators.equals(dominators.get(block))) {
                    dominators.put(block, newDominators);
                    changed = true;
                }
            }
        }

        // Compute dominance frontiers
        for (Map.Entry<String, List<Operation>> entry : basicBlocks.entrySet()) {
            String block = entry.getKey();
            Set<String> frontier = new HashSet<>();
            for (String succ : blockSuccessors.getOrDefault(block, new ArrayList<>())) {
                for (String pred : getPredecessors(succ)) {
                    if (!dominators.get(succ).contains(pred)) {
                        frontier.add(succ);
                        break;
                    }
                }
            }
            dominanceFrontiers.put(block, frontier);
        }

        printDominanceResults();
    }

    private static List<String> getPredecessors(String block) {
        List<String> predecessors = new ArrayList<>();
        for (Map.Entry<String, List<String>> entry : blockSuccessors.entrySet()) {
            if (entry.getValue().contains(block)) {
                predecessors.add(entry.getKey());
            }
        }
        return predecessors;
    }
    private static void parseLirFile(String filePath, String functionName) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String currentBlock = null;
            boolean isFunction = false;
            boolean isStruct = false;

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
                        String[] variables = paramSubstring.toString().split(",\\s*");
                        for (String varDeclaration : variables) {
                            String[] parts = varDeclaration.split(":");
                            String varName = parts[0].trim();
                            // Should get all types
                            String type = parts[1].trim();
                            VariableState newState = new VariableState();
                            newState.setType(type);
                            if (type.startsWith("&")) {
                                newState.setPointsTo(type.substring(1));
                            }
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
                        basicBlocks.putIfAbsent(currentBlock, new ArrayList<>());
                    } else if (line.startsWith("let ")) {
                        String variablesPart = line.substring("let ".length());
                        StringBuilder transformedPart = new StringBuilder();
                        int parenthesisLevel = 0;
                        for (char c : variablesPart.toCharArray()) {
                            if (c == '(') {
                                parenthesisLevel++;
                            }else if (c == ')'){
                                parenthesisLevel--;
                            } else if (c == ',' && parenthesisLevel > 0){
                                c = '|';
                            }
                            transformedPart.append(c);
                        }
                        String[] variables = transformedPart.toString().split(",\\s*");
                        for (String varDeclaration : variables) {
                            String[] parts = varDeclaration.split(":");
                            String varName = parts[0].trim();
                            // Should get all types
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
                        Operation newOp = new Operation(currentBlock, line);
                        basicBlocks.get(currentBlock).add(newOp);
                        String[] parts = line.split(" ");
                        TreeMap<String, String> varsInBlock = blockVars.get(currentBlock);
                        for (int i = 0; i < parts.length; i++) {
                            String part = parts[i];
                            if (variableStates.containsKey(part)) {
                                varsInBlock.put(part, "");
                            }
                        }
                        if (parts.length > 3) {
                            String address = parts[0];
                            String addressTakenVar = parts[3];
                            variableStates.get(address).setPointsTo(addressTakenVar);
                            if(variableStates.containsKey(addressTakenVar)) {
                                addressTakenVariables.add(addressTakenVar);
                            }
                        }
                    } else {
                        TreeMap<String, String> varsInBlock = blockVars.get(currentBlock);
                        String[] parts = line.split(" ");
                        for (int i = 0; i < parts.length; i++) {
                            String part = parts[i];
                            if (variableStates.containsKey(part)) {
                                VariableState thisVar = variableStates.get(part);
                                varsInBlock.put(part, "");
                            }
                        }
                        if (currentBlock != null) {
                            Operation newOp = new Operation(currentBlock, line);
                            basicBlocks.get(currentBlock).add(newOp);
                            if (line.startsWith("$jump")) {
                                String targetBlock = extractTargetBlock(line);
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                            }else if (line.startsWith("$branch")) {
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[2]); // trueBlock
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[3]); // falseBlock
                            }else if (line.contains("then")){
                                String targetBlock = line.substring(line.lastIndexOf("then") + 5).trim();
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                            }
                        }else{
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

    private static void printDominanceResults() {
        // Sort the basic block names alphabetically
        for (Map.Entry<String, Set<String>> entry : dominanceFrontiers.entrySet()) {
            System.out.println(entry.getKey() + " -> " + entry.getValue());
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
        controlDominanceAnalysis(lirFilePath, functionName);
    }
}