#! /bin/bash

for file in paptests/Wrong/*
do
        echo $file
        ##name=${file##*/}
        ./Main.byte < $file


	    echo ""
        read -p "Continue (y/n)?" choice
        case "$choice" in
        "") ./out; read s ;;
        * ) ;;
        esac
done
