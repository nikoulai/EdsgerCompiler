#! /bin/bash

for file in paptests/Correct/*.eds
do
        echo $file
        ##name=${file##*/}
        ./Main.byte $file


	    echo ""
        read -p "Continue (y/n)?" choice
        case "$choice" in
        "") ${file%.*}; read s ;;
        * ) ;;
        esac
done
