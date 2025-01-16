#!/bin/bash

TMP_OUT=$(mktemp)
TMP_ERR=$(mktemp)

for file in ./good/*.jez
do
        ./Interpreter $file > $TMP_OUT 2> $TMP_ERR

        if diff ${file%jez}out $TMP_OUT>/dev/null
        then echo -e "OK";
        else echo -e "ERROR IN OUTPUT (test $file)"
        fi

        if diff ${file%jez}err $TMP_ERR>/dev/null
        then echo -e "OK";
        else echo -e "ERROR IN ERROR (test $file)"
        fi

        echo ""
done