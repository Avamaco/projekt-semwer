#!/bin/bash

for file in ./bad/*.jez
do
        ./Interpreter $file > ${file%jez}out 2> ${file%jez}err
        echo "Output generated for $file"
done