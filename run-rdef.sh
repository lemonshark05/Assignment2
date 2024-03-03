#!/bin/bash

#
#if [ "$#" -lt 2 ]; then
#    echo "Usage: ./run-rdef.sh <LIR file> <JSON file> <function name>"
#    exit 1
#fi

LIR_FILE="$1"
JSON_FILE="$2"
FUNCTION_NAME="$3"

javac DataFlowRdef.java State.java ProgramPoint.java VariableState.java
java DataFlowRdef "$LIR_FILE" "$JSON_FILE" "$FUNCTION_NAME"

#if [ -f "$LIR_FILE" ]; then
#    javac DataFlowControl.java State.java VariableState.java
#    java DataFlowConstants "$LIR_FILE" "$JSON_FILE" "$FUNCTION_NAME"
#elif [ -f "$JSON_FILE" ]; then
#  pass
#else
#    echo "Error: Neither LIR nor JSON file exists."
#    exit 1
#fi