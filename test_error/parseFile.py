#!/usr/bin/env python
# coding: utf-8
import sys
from log import logger
import re

def checkFile(argv):
    if argv == []:
        logger.error("Pas de fichier en argument, exit")
        sys.exit(1)
    try:  # On essaye de convertir l'année en entier
        file = open(argv[0], 'r')
    except:
        print("Erreur lors de l ouverture du fichier,exit")
        sys.exit(1)

    regex = re.compile(r"#.*", re.IGNORECASE)
    file2 = regex.sub("", file.read())
    file2 = file2.replace(" ", "")
    file2 = file2.replace("!!", "")
    #suppression ligne vide
    while file2.find('\n\n') != -1:
        file2 = file2.replace('\n\n', '\n')
    # suppresion premier saut de ligne
    test = re.findall("^\n", file2)
    if len(test) > 0 and test[0] == '\n':
        file2 = file2.replace('\n', '', 1)
   # logger.debug('file2\n {}'.format(file2))

    # if file2[0] == '\n':
    #     file2.replace('\n', '')

    split = file2.split('\n')
    for line in split:
        if line == '':
            continue
        elif '=>' in line or line[0] == '=' or line[0] == '?':
            continue
        else:
            logger.info('error in line {}'.format(line))
            sys.exit(1)

    #sys.exit(1)
    #check une seul ligne d initialisation
    equalTab = re.findall("(?<=\n=).*", file2)
    if len(equalTab) > 1:
        print("Erreur deux lignes d initialisation")
        sys.exit(0)
    #sys.exit(1)
    file.close()
    return file2
