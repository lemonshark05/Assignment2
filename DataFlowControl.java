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

    static TreeSet<String> basicBlocks = new TreeSet<>();
    static TreeMap<String, List<String>> blockSuccessors = new TreeMap<>();
    static TreeMap<String, TreeSet<String>> predecessors = new TreeMap<>();
    static TreeMap<String, TreeSet<String>> dominators = new TreeMap<>();
    static TreeMap<String, TreeSet<String>> postDominators = new TreeMap<>();
    static TreeMap<String, List<String>> reverseSuccessors = new TreeMap<>();
    static TreeMap<String, TreeSet<String>> dominanceFrontiers = new TreeMap<>();


    public static void controlDominanceAnalysis(String filePath, String functionName) {
        Queue<String> worklist = new PriorityQueue<>();

        parseLirFile(filePath, functionName);
        predecessors.put("entry", new TreeSet<>());
        String postEntry = "entry";
        for (String block : basicBlocks) {
            if (blockSuccessors.get(block) != null) {
                for (String target : blockSuccessors.get(block)) {
                    predecessors.computeIfAbsent(target, k -> new TreeSet<>()).add(block);
                }
            }
        }
        //Compute dominators
        computeDominators();
//        for (String block : basicBlocks) {
//            System.out.println(block + ", Dominators: " + dominators.get(block));
//        }
//        for (String block : basicBlocks) {
//            System.out.println(block + ", Dominators: " + dominators.get(block));
//        }
        for (String block : basicBlocks) {
            if(!block.equals("entry") && dominators.get(block).size() == 1 ){
                postEntry = block;
            }
            dominanceFrontiers.put(block, new TreeSet<>());
        }

        for (String curBlock : basicBlocks) {
            TreeSet<String> bbDoms = dominators.get(curBlock); // Get the dominators of the block
            TreeSet<String> strictBbDoms = new TreeSet<>(bbDoms);
            strictBbDoms.remove(curBlock); // Remove the block itself to make it 'strict'

            // Iterate over each predecessor of the current block
            for (String pred : predecessors.getOrDefault(curBlock, new TreeSet<>())) {
                // Get the dominators of the predecessor
                TreeSet<String> predDoms = dominators.get(pred);

                TreeSet<String> relevantPredDoms = new TreeSet<>(predDoms);
                relevantPredDoms.removeAll(strictBbDoms);

                for (String predDom : relevantPredDoms) {
                    dominanceFrontiers.computeIfAbsent(predDom, k -> new TreeSet<>()).add(curBlock);
                }
            }
        }

        printDominanceResults();
    }

    public static void computeDominators() {
        for (String block : basicBlocks) {
            dominators.put(block, basicBlocks);
        }
        // The entry block is only dominated by itself
        TreeSet<String> entryDominators = new TreeSet<>();
        entryDominators.add("entry");
        dominators.put("entry", entryDominators);

        boolean changed = true;
        while (changed) {
            changed = false;
            for (String block : basicBlocks) {
                if (block.equals("entry")) continue; // Skip the entry block

                TreeSet<String> newDominators = new TreeSet<>(basicBlocks);
                for (String pred : predecessors.get(block)) {
                    TreeSet set = dominators.get(pred);
                    newDominators.retainAll(dominators.get(pred));
                }
                // a block dominates itself
                newDominators.add(block);

                if (!dominators.get(block).equals(newDominators)) {
                    dominators.put(block, newDominators);
                    changed = true;
                }
            }
        }
    }

    private static void parseLirFile(String filePath, String functionName) {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String currentBlock = null;
            boolean isFunction = false;
            boolean isStruct = false;

            String line;
            while ((line = reader.readLine()) != null) {
                line = line.trim();

                if (line.length() == 0) continue;
                if (line.startsWith("fn " + functionName)) {
                    isFunction = true;
                    if (line.contains(":") && line.contains("(")) {
                        String paramSubstring = line.substring(line.indexOf('(') + 1, line.indexOf(')'));
                        StringBuilder transformedPart = new StringBuilder();
                        int parenthesisLevel = 0;
                        for (char c : paramSubstring.toCharArray()) {
                            if (c == '(') {
                                parenthesisLevel++;
                            } else if (c == ')') {
                                parenthesisLevel--;
                            } else if (c == ',' && parenthesisLevel > 0) {
                                c = '|';
                            }
                            transformedPart.append(c);
                        }
                        String[] variables = paramSubstring.split(",\\s*");
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
                        }
                    }
                } else if (isFunction && line.startsWith("}")) {
                    isFunction = false;
                    currentBlock = null;
                } else if (line.startsWith("struct ")) {
                    isStruct = true;
                } else if (isStruct && line.startsWith("}")) {
                    isStruct = false;
                } else if (!isFunction && !isStruct && line.matches("^\\w+:int$")) {

                } else if (isFunction) {
                    if (line.matches("^\\w+:")) {
                        currentBlock = line.replace(":", "");
                        basicBlocks.add(currentBlock);
                    } else if (line.startsWith("let ")) {
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
                    } else {
                        String[] parts = line.split(" ");
                        if (currentBlock != null) {
                            if (line.startsWith("$jump")) {
                                String targetBlock = extractTargetBlock(line);
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                                reverseSuccessors.computeIfAbsent(targetBlock, k -> new ArrayList<>()).add(currentBlock);
                            } else if (line.startsWith("$branch")) {
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[2]); // trueBlock
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(parts[3]); // falseBlock
                                reverseSuccessors.computeIfAbsent(parts[2], k -> new ArrayList<>()).add(currentBlock); // trueBlock
                                reverseSuccessors.computeIfAbsent(parts[3], k -> new ArrayList<>()).add(currentBlock); // falseBlock
                            } else if (line.contains("then")) {
                                String targetBlock = line.substring(line.lastIndexOf("then") + 5).trim();
                                blockSuccessors.computeIfAbsent(currentBlock, k -> new ArrayList<>()).add(targetBlock);
                                reverseSuccessors.computeIfAbsent(targetBlock, k -> new ArrayList<>()).add(currentBlock);
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

    private static void printDominanceResults() {
        // Sort the basic block names alphabetically
        for (Map.Entry<String, TreeSet<String>> entry : dominanceFrontiers.entrySet()) {
            // Convert the Set to a String with square brackets
            String formattedValue = entry.getValue().toString()
                    .replace("[", "{")
                    .replace("]", "}");
            System.out.println(entry.getKey() + " -> " + formattedValue);
        }
    }

    public static void main(String[] args) {
        if (args.length < 2) {
            System.out.println("Usage: java DataFlowConstants <lir_file_path> <json_file_path> <function_name>");
            System.exit(1);
        }
        String lirFilePath = args[0];
        String functionName = "test";
        if (args.length > 2 && args[2].length() != 0) {
            functionName = args[2];
        }
        controlDominanceAnalysis(lirFilePath, functionName);
    }
}