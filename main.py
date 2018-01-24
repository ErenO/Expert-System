#!/usr/bin/env python
# coding: utf-8
from log import *
import re
import sys
import collections
import copy
import find_rule as fr
import random
from parseFile import checkFile

def and_rule(a, b):
    ret = a and b
    return ret

def impl(a):
    if a:
        return (True)
    else:
        return (None)

def xor_rule(a, b):
    ret = (a and not b) or (not a and b)
    return ret

def or_rule(a, b):
    ret = a or b
    return ret

def not_rule(a):
    return (not a)

def implicationDic(equ):
    # dictionnaire des implications True => ou false <=>
    dic = {}
    index = 0
    for i in equ:
        if i.startswith('=>'):
            dic[index] = {"equ": i, "val": True}
        else:
            dic[index] = {"equ": i, "val": False}
        index += 1
    return dic

def letterForEachLine(file):
    # tableau tous les lettre pour chaque ligne
    letterLine = []
    file_content = file.split('\n')
    for lines in file_content[0:]:
        reg = re.findall("[A-Z]", lines)
        letterLine.append(reg)
    return letterLine

def letterDicValue(equal, letterFile):
    # dictionnaire des lettres avec leurs valeurs
    dic = {}
    for i in letterFile:
        if equal[0].find(i) != -1:
            dic[i] = {"letter": i, "val": True, "constant": True}
        else:
            dic[i] = {"letter": i, "val": False, "constant": False}
    dic["1"] = {"letter": "1", "val": True, "constant": True}
    dic["0"] = {"letter": "0", "val": False, "constant": True}
    return dic

def checkLine(letter, leftTab, equTab, rightTab):
    logger.debug("{}:    {} {} {}".format(letter, leftTab, equTab, rightTab))
    Max = len(leftTab)
    i = 0
    while i < Max:
        logger.debug("( {}  ) {}".format(leftTab[i].count("("), leftTab[i].count(")")))
        if leftTab[i].count("(") != leftTab[i].count(")"):
            logger.error("error in {} {} {}, number of parentheses".format(leftTab[i], equTab[i], rightTab[i]))
            sys.exit(1)
        logger.debug("( {}  ) {}".format(rightTab[i].count("("), rightTab[i].count(")")))
        if rightTab[i].count("(") != rightTab[i].count(")"):
            logger.error("error in {} {} {}, number of parentheses".format(leftTab[i], equTab[i], rightTab[i]))
            sys.exit(1)

        logger.debug('equtab {}'.format(equTab[i]))

        if equTab[i].find('<=>') != -1:
            logger.debug('dans if')
            if (leftTab[i].find(letter) != -1) and (rightTab[i].find(letter) == -1):
                logger.debug('dans if')
                logger.debug("{}:    {} {} {}".format(letter, leftTab[i], equTab[i], rightTab[i]))
                tmp = leftTab[i]
                leftTab[i] = rightTab[i]
                rightTab[i] = tmp
                logger.debug("{}:    {} {} {}".format(letter, leftTab[i], equTab[i], rightTab[i]))
        i = i + 1


#pour avoir la position des lettres de la query
def findQueryLetter(query, left, right):
    dict = {}
    lq = list(query[0])
    i = 0
    tab = []

    for l in lq:
        i = 0
        tab = []
        dict[l] = {"letter": l, "right": []}
        for r in right:
            if l in r:
                if "right" in dict:
                    tab = dict[l]["right"]
                if i not in tab:
                    tab.append(i)
                    dict[l] = {"letter": l, "right": tab}
            i += 1
    return dict

def letterInRight(right):
    listLetter = set(re.findall("[A-Z]", right))
    # logger.debug('ret letter in right {}'.format(listLetter))
    return listLetter

def findLetterRightSide(letter, right):
    tab = []
    i = 0
    for r in right:
        if letter in r:
            tab.append(i)
        i += 1
    return tab

def printAll(dicEqu, dic, left, right, equal, query, letterFile, equ, letterLine):
    logger.debug("dicEqu {}".format(dicEqu))
    logger.debug("left {}".format(left))
    logger.debug("right {}".format(right))
    logger.debug("ewu {}".format(equ))
    logger.debug("letterLine {}".format(letterLine))
    logger.debug("equal[0] {}".format(equal))
    logger.debug("query {}".format(query))
    logger.debug("letterFile {}".format(letterFile))
    logger.debug("dic {}".format( dic))


#fonction qui repond a la query de type B + A => E | F
def solveQuery(dict, leftTab, rightTab, alphabet, line, lineTab, equTab):
    Ret = collections.namedtuple('Ret', ['alpha', 'left'])
    r = Ret(alphabet, left=leftTab[line])
    # logger.debug("left {}".format(leftTab))
    if len(leftTab[line]) > 1:
        retExp = solveExp(r, dict, leftTab[line], leftTab, rightTab, lineTab, equTab)
    else:
        if alphabet[leftTab[line]]["constant"] == False:
            r = parseRightLetter(alphabet[leftTab[line]]["letter"], leftTab, rightTab, r, lineTab, equTab)
            retExp = "1" if r.alpha[leftTab[line]]["val"] == True else "0"
        elif alphabet[leftTab[line]]["val"] == True: # j'ai ecrit 0 au lieu de line
            retExp = "1"
        else:
            retExp = "0"
    r = Ret(alphabet, left=retExp)
    return r

#fonction recursive qui resout les expression type Q + (A | (D + B) + H) + E
def solveExp(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    if currentLine == "0" or currentLine == "1":
        return currentLine
    currentLine = fr.findParanthese(r, dict, currentLine, leftTab, rightTab, lineTab, equTab)
    currentLine = fr.findExclamation(r, dict, currentLine, leftTab, rightTab, lineTab, equTab)
    currentLine = fr.findAnd(r, dict, currentLine, leftTab, rightTab, lineTab, equTab)
    currentLine = fr.findOr(r, dict, currentLine, leftTab, rightTab, lineTab, equTab)
    currentLine = fr.findXor(r, dict, currentLine, leftTab, rightTab, lineTab, equTab)
    return currentLine   #return le string de l exp, a la fin on aura 0 ou 1

#random degueu
def recurs(tab, number):
    i = 0
    tab2 = []
    for i in range(0, number):
        rand = random.randint(0, 1)
        if rand == 1:
            tab2.append(True)
        else:
            tab2.append(False)
    if tab2 not in tab:
        tab.append(tab2)
    return tab

def random_tab(nbLetter):
    tab = []
    i = 0
    pb = pow(2, nbLetter)
    while (len(tab) < pb):
        tab = recurs(tab, nbLetter)
        i += 1
    return tab

def fetchVarLetter(dict, leftTab, rightTab, alphabet, line, lineTab, equTab):
    rightLetter = re.findall("[A-Z]", rightTab[line])
    Ret = collections.namedtuple('Ret', ['letterTab', 'randomTab'])
    tab = []
    for letter in rightLetter:
        if alphabet[letter]["constant"] == False:
            if letter not in tab:
                tab.append(letter)
    randomTab = random_tab(len(tab))
    r = Ret(tab, randomTab= randomTab)
    return r

#bruteforce pour le coté droit, il teste True, apres False
def solveRightSide(dict, leftTab, rightTab, alphabet, line, lineTab, equTab):
    if equTab[line] == '=>':
        return solveImplicationRight2(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
    elif equTab[line] == '<=>':
        return solveEquivalenceRight2(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
    else:
        logger.error('ni implication ni equivqlence')
    return


def solveEquivalenceRight2(dict, leftTab, rightTab, alphabet, line, lineTab, equTab):
    Ret = collections.namedtuple('Ret', ['alpha', 'left'])
    r = Ret(alphabet, left=leftTab[line])
    # const = alphabet[letter]["val"]
    if leftTab[line] == "0":
        tmp = False
    else:
        tmp = True
    if len(rightTab[line]) > 1:
        possibility = fetchVarLetter(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
        if len(possibility.letterTab) != 0:
            for lineRand in possibility.randomTab:
                for i in range(0, len(possibility.letterTab)):
                    alphabet[possibility.letterTab[i]]["val"] = lineRand[i]
                str = solveExp(r, dict, rightTab[line], leftTab, rightTab, lineTab, equTab)
                if str == leftTab[line]:
                    for i in range(0, len(possibility.letterTab)):
                        alphabet[possibility.letterTab[i]]["constant"] = True
                    r = Ret(alphabet, left=leftTab[line])
                    break
        else:
            str = solveExp(r, dict, rightTab[line], leftTab, rightTab, lineTab, equTab)
            if str != leftTab[line]:
                print 'error conflicts rules'
                sys.exit(1)

    else:
        letter = rightTab[line]
        #gestion des conflit entre ligne
        if alphabet[letter]["constant"] == True:
            if tmp != alphabet[letter]["val"]:
                logger.info("Two values for : {}".format(letter))
                sys.exit(0)
            if alphabet[letter]["val"] == True and leftTab[line] == "0" :
                changeLetter(alphabet, letter, None)
            elif alphabet[letter]["val"] == False and leftTab[line] == "1":
                changeLetter(alphabet, letter, None)
            return r
        if leftTab[line] == "1":
            changeLetter(alphabet, letter, True)
        else:
            changeLetter(alphabet, letter, False)
    return r

def changeLetter(alphabet, letter, val):
    if alphabet[letter]["constant"] == True:
        if alphabet[letter]["val"] != val:
            print 'changeLetter error, on ne peut changer une letter constant'
            sys.exit(1)
    alphabet[letter]["val"] = val
    if val != None:
        alphabet[letter]["constant"] = True
    return alphabet

def solveImplicationRight2(dict, leftTab, rightTab, alphabet, line, lineTab, equTab):
    Ret = collections.namedtuple('Ret', ['alpha', 'left'])
    r = Ret(alphabet, left=leftTab[line])
    if leftTab[line] == "0":
        listLetterRight = letterInRight(rightTab[line])
        for letter in listLetterRight:
            if alphabet[letter]['constant'] == False:
                changeLetter(alphabet, letter, None)
        r = Ret(alphabet, left=leftTab[line])
        return r

    if len(rightTab[line]) > 1:
        possibility = fetchVarLetter(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
        if len(possibility.letterTab) != 0:
            for lineRand in possibility.randomTab:
                for i in range(0, len(possibility.letterTab)):
                    alphabet[possibility.letterTab[i]]["val"] = lineRand[i]
                str = solveExp(r, dict, rightTab[line], leftTab, rightTab, lineTab, equTab)
                if str == leftTab[line]:
                    for i in range(0, len(possibility.letterTab)):
                        alphabet[possibility.letterTab[i]]["constant"] = True
                    r = Ret(alphabet, left=leftTab[line])
                    break
        else:
            str = solveExp(r, dict, rightTab[line], leftTab, rightTab, lineTab, equTab)
            if leftTab[line] == '1' and str != leftTab[line]:
                print 'error conflicts rules'
                sys.exit(1)

    else:
        letter = rightTab[line]
        if leftTab[line] == '0':
            changeLetter(alphabet, letter, None)
            return r

        #gestion des conflit entre ligne
        if alphabet[letter]["constant"] == True:
            if alphabet[letter]["val"] == False and leftTab[line] == "1":
                logger.debug('conflit entre ligne')
                changeLetter(alphabet, letter, None)
            return r
        if leftTab[line] == "1":
            changeLetter(alphabet, letter, True)
        else:
            changeLetter(alphabet, letter, None)
    return r

def parseRightLetter(letter, leftTab, rightTab, r, lineTab, equTab):
    tab = findLetterRightSide(letter, rightTab)
    Ret = collections.namedtuple('Ret', ['alpha', 'left'])
    for line in tab:
        if lineTab[line] == False:
            r = Ret(r.alpha, left=leftTab[line])
            r = solveQuery(dict, leftTab, rightTab, r.alpha, line, lineTab, equTab)
            leftTab[line] = r.left
            lineTab[line] = True
            r = solveRightSide({}, leftTab, rightTab, r.alpha, line, letter, lineTab, equTab)
    return r

#dict : dict des lettres avec les lignes
#leftTab
#rightTab
#alphabet : dict des letter avec leur valeur et constant ou non
def parseQuery(dict, leftTab, rightTab, alphabet, queryTab, lineTab, equTab):
    Ret = collections.namedtuple('Ret', ['alpha', 'left'])
    #dict indique la position des queries
    tmp = copy.deepcopy(alphabet)
    tmp2 = list(lineTab)
    for letter in dict:
        #on accede au contenu de la key de dict et il faut deux for pour ça
        for line in dict[letter]["right"]:
            if lineTab[line] == False:
                r = Ret(alphabet, left=leftTab[line])
                r = solveQuery(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
                leftTab[line] = r.left
                lineTab[line] = True
                solveRightSide(dict, leftTab, rightTab, alphabet, line, letter, lineTab, equTab)
        alphabet = copy.deepcopy(tmp)
        lineTab = list(tmp2)
    return alphabet

# Tri les lignes dans l ordre d execution
#dict : dict des lettres avec les lignes
#leftTab
#rightTab
#alphabet : dict des letter avec leur valeur et constant ou non
def parseQuery2(letter, dict, leftTab, rightTab, alphabet, queryTab, lineTab, equTab):
    ret = []
    # les ligne ou gauche na que des constant en premier
    for index in range(len(leftTab)):
        listLetterLeft = set(re.findall("[A-Z]", leftTab[index]))
        addLine = True
        for letter3 in listLetterLeft:
            if alphabet[letter3]['constant'] == False or lineTab[index] == True:
                addLine = False
                break
        if addLine:
            ret.append(index)
            lineTab[index] = True
    tab = findLetterRightSide(letter, rightTab)

    for line in tab:
        if lineTab[line] == True:
            continue

        lineTab[line] = True
        listLetterLeft = set(re.findall("[A-Z]", leftTab[line]))
        for letter2 in listLetterLeft:
            ret.extend(parseQuery2(letter2, dict, leftTab, rightTab, alphabet, queryTab, lineTab, equTab))
        for i in tab:
            if i not in ret:
                ret.append(i)
    return ret

def main(argv):
    file2 = checkFile(argv)
    leftTab = re.findall(".*[A-Z()!]\s*(?=\=>)|.*[A-Z()!]\s*(?=<\=>)", file2)
    rightTab = re.findall("(?<=\=>).*[A-Z()!]\s*(?=\n)|(?<=<\=>).*[A-Z()!]\s*(?=\n)", file2)
    equTab = re.findall("=>|<=>", file2)
    equalTab = re.findall("(?<=\n=)[A-Z\s]*[\n]", file2)
    queryTab = re.findall("(?<=\n\?)[A-Z]*$", file2)
    errChar = re.findall("[^A-Z<=>+|\(\)\^\!?\s\#]", file2)
    errEqual = re.findall("(?<=\n=)((?![A-Z]).)*", file2)
    ruleLines = re.findall(".*(?=\=>).*|.*(?=<\=>).*", file2)
    errLeft = re.findall("(?<=\n)[#\nA-Z()!]|^[#\nA-Z()!]", file2)
    errRight = re.findall("(?<=<=>)[#\nA-Z()!]|(?<=\=>)[#\nA-Z()!]", file2)
    r = re.compile("[A-Z]{2,}")
    newlist = filter(r.match, ruleLines)
    logger.info(file2)

    logger.debug('{} {} {}'.format(leftTab, equTab, rightTab ))
    if len(leftTab) == 0 or len(rightTab) == 0:
        print "error rule"
        sys.exit(0)
    elif len(equTab) == 0:
        print "error equivalence"
        sys.exit(0)
    elif (len(errEqual) > 0 and errEqual[0] != "") or len(equalTab) == 0:
        print "error equal"
        sys.exit(0)
    elif len(queryTab) == 0:
        print "error query"
        sys.exit(0)
    elif len(errChar) != 0:
        print "None accepted character"
        sys.exit(0)
    elif len(newlist) != 0:
        print "Error syntaxe"
        sys.exit(0)
    elif len(equTab) != len(leftTab) or len(leftTab) != len(rightTab) or len(leftTab) != len(errLeft) or len(rightTab) != len(errRight):
        print "Error syntaxe"
        sys.exit(0)
    dict = findQueryLetter(queryTab, leftTab, rightTab)
    for letter in dict:
        leftTab = re.findall(".*[A-Z()!]\s*(?=\=>)|.*[A-Z()!]\s*(?=<\=>)", file2)
        rightTab = re.findall("(?<=\=>).*[A-Z()!]\s*(?=\n)|(?<=<\=>).*[A-Z()!]\s*(?=\n)", file2)
        equTab = re.findall("=>|<=>", file2)
        equalTab = re.findall("(?<=\n=)[A-Z\s]*[\n]", file2)
        queryTab = re.findall("(?<=\n\?)[A-Z\s]$", file2)
        checkLine(letter, leftTab, equTab, rightTab)
        # tableau tous les lettre pour chaque ligne
        letterLine = letterForEachLine(file2)
        #tableau de booleen pour chaque ligne vu, True ou False
        lineTab = [False] * len(letterLine)
        #toutes lettre du fichier avec doublon
        letterFile = []
        letterFile = re.findall("[A-Z]", file2)
        # dict pour le savoir si c'est => ou <=>
        dicEqu = implicationDic(equTab)
        # dictionnaire des lettres avec leurs valeurs
        alphabet = letterDicValue(equalTab, letterFile)
        #dict indique la position des queries
        sortedLine = parseQuery2(letter, dict, leftTab, rightTab, alphabet, queryTab, lineTab, equTab)
        # logger.debug('sorted Line {}'.format(sortedLine))
        for line in sortedLine:
            r = solveQuery(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
            leftTab[line] = r.left
            lineTab[line] = True
            solveRightSide(dict, leftTab, rightTab, alphabet, line, lineTab, equTab)
        queryResult2(letter, alphabet)

#logle resultat de la query
def queryResult(query, dic):
    q = list(query[0])
    tmp = None
    for q in q:
        tmp = dic[q]["val"]
        if (tmp == None):
            logger.info("{} is undetermined".format(q))
        elif (tmp == True):
            logger.info("{} is True".format(q))
        else:
            logger.info("{} is False".format(q))

#logle resultat de la query pour une letter
def queryResult2(letter, dic):
    tmp = dic[letter]["val"]
    ## a la fin si letter indeterminer , elle est false
    if (tmp == None):
        logger.info("\n|-------------------|\n"
                    "|                   |\n"
                    "| {} is False        |\n"
                    "|                   |\n"
                    "|-------------------|".format(letter))
    elif (tmp == True):
        logger.info("\n|-------------------|\n"
                    "|                   |\n"
                    "| {} is True         |\n"
                    "|                   |\n"
                    "|-------------------|".format(letter))
    else:
        logger.info("\n|-------------------|\n"
                    "|                   |\n"
                    "| {} is False        |\n"
                    "|                   |\n"
                    "|-------------------|".format(letter))

if __name__ == "__main__":
    main(sys.argv[1:])
