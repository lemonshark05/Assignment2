#!/bin/bash

#set -e

## $1 = lir program file; $2 = json format file; $3 = function to analyze
#./my_binary "$1" "$2" "$3"

LIR_FILE="$1"
JSON_FILE="$2"
FUNCTION_NAME="$3"

javac DataFlowControl.java State.java ProgramPoint.java VariableState.java
java DataFlowControl "$LIR_FILE" "$JSON_FILE" "$FUNCTION_NAME"