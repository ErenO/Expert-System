#!/usr/bin/env python
# coding: utf-8
import re
import sys
import collections
from main import *
import log


def findAnd(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    # logger.debug("__debut and__  {}".format(currentLine))
    # logger.debug("YYYYYYY {}".format( r))
    positionOP = currentLine.find('+')
    if positionOP == -1:
        return currentLine
    letter1 = currentLine[positionOP - 1]
    letter2 = currentLine[positionOP + 1]
    if not letter1.isalpha() and letter1.find("!") == -1 and letter1.find("0") == -1 and letter1.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter1))
        sys.exit(1)
    if not letter2.isalnum()and letter2.find("!") == -1 and letter2.find("0") == -1 and letter2.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter2))
        sys.exit(1)
    # # logger.debug("letter1 {} {}".format(letter1, r.alpha[letter1]["constant"]))
    # if r.alpha[letter1]["constant"] == False:
    #     r = parseRightLetter(letter1, leftTab, rightTab, r, lineTab, equTab)
    # if r.alpha[letter2]["constant"] == False:
    #     r = parseRightLetter(letter2, leftTab, rightTab, r, lineTab, equTab)
    # logger.debug("bool {}".format(r.alpha[letter1]['val']))
    result =  r.alpha[letter1]["val"] and r.alpha[letter2]["val"]
    # logger.debug("result {}".format( result))
    if result == True:
        result = "1"
    else:
        result = "0"
    sub = currentLine.replace(letter1+"+"+letter2, result, 1)
    #sub = str[:letter1]+result+str[letter2]
    # logger.debug("sub {}".format(sub))
    newstr = solveExp(r, dict, sub, leftTab, rightTab, lineTab, equTab)
    # logger.debug("newstr {}".format(newstr))
    return newstr

def findExclamation(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    # logger.debug("__debut exclamation__  {}".format(currentLine))
    positionOP = currentLine.find('!')
    if positionOP == -1:
        return currentLine
    letter = currentLine[positionOP + 1]

    if not letter.isalpha() and letter.find("!") == -1 and letter.find("0") == -1 and letter.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter))
        sys.exit(1)
    # logger.debug("letter1 {}".format(letter))
    # logger.debug("bool {}".format( r.alpha[letter]['val']))
    # if r.alpha[letter]["constant"] == False:
    #     r = parseRightLetter(letter, leftTab, rightTab, r, lineTab, equTab)
    result = not r.alpha[letter]["val"]
    # logger.debug("result  {}".format( result))
    if result == True:
        result = "1"
    else:
        result = "0"
    sub = currentLine.replace("!"+letter, result, 1)
    #sub = str[:letter1]+result+str[letter2]
    # logger.debug("sub {}".format( sub))
    newstr = solveExp(r, dict, sub, leftTab, rightTab, lineTab, equTab)
    # logger.debug("newstr {}".format(newstr))
    return newstr

def findOr(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    # logger.debug("__debut Or__  {}".format( currentLine))
    positionOP = currentLine.find('|')
    if positionOP == -1:
        return currentLine
    letter1 = currentLine[positionOP - 1]
    letter2 = currentLine[positionOP + 1]
    if not letter1.isalpha() and letter1.find("!") == -1 and letter1.find("0") == -1 and letter1.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter1))
        sys.exit(1)
    if not letter2.isalnum()and letter2.find("!") == -1 and letter2.find("0") == -1 and letter2.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter2))
        sys.exit(1)
    # # logger.debug("letter1 {}".format(letter1 ))
    # if r.alpha[letter1]["constant"] == False:
    #     logger.debug("letterLine1 {}".format(letter1))
    #     r = parseRightLetter(letter1, leftTab, rightTab, r, lineTab, equTab)
    # if r.alpha[letter2]["constant"] == False:
    #     logger.debug("letterLine2")
    #     r = parseRightLetter(letter2, leftTab, rightTab, r, lineTab, equTab)
    # logger.debug("bool {}".format(r.alpha[letter1]['val']))
    # logger.debug("bool {}".format(r.alpha[letter1]['val']))
    result = or_rule(r.alpha[letter1]["val"], r.alpha[letter2]["val"])
    # logger.debug("result  {}".format( result))
    if result == True:
        result = "1"
    else:
        result = "0"
    sub = currentLine.replace(letter1+"|"+letter2, result, 1)
    #sub = str[:letter1]+result+str[letter2]
    # logger.debug("sub {}".format( sub))
    newstr = solveExp(r, dict, sub, leftTab, rightTab, lineTab, equTab)
    # logger.debug("newstr {}".format( newstr))
    return newstr

def findXor(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    # logger.debug("__debut xor__  {}".format( currentLine))
    positionOP = currentLine.find('^')
    if positionOP == -1:
        return currentLine
    letter1 = currentLine[positionOP - 1]
    letter2 = currentLine[positionOP + 1]
    if not letter1.isalpha() and letter1.find("!") == -1 and letter1.find("0") == -1 and letter1.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter1))
        sys.exit(1)
    if not letter2.isalnum()and letter2.find("!") == -1 and letter2.find("0") == -1 and letter2.find("1") == -1:
        logger.info('error in {} , {} nest pas une lettre'.format(currentLine, letter2))
        sys.exit(1)
    # logger.debug("letter1 {}".format(letter1 ))
    # if r.alpha[letter1]["constant"] == False:
    #     logger.debug("letterLine1 {}".format( letter1))
    #     r = parseRightLetter(letter1, leftTab, rightTab, r, lineTab, equTab)
    # if r.alpha[letter2]["constant"] == False:
    #     logger.debug("letterLine2")
    #     r = parseRightLetter(letter2, leftTab, rightTab, r, lineTab, equTab)
    # logger.debug("bool {}".format(r.alpha[letter1]['val']))
    # logger.debug("bool {}".format(r.alpha[letter1]['val']))
    result = xor_rule(r.alpha[letter1]["val"], r.alpha[letter2]["val"])
    # logger.debug("result {}".format( result))
    if result == True:
        result = "1"
    else:
        result = "0"
    sub = currentLine.replace(letter1+"^"+letter2, result, 1)
    #sub = str[:letter1]+result+str[letter2]
    # logger.debug("sub {}".format(sub))
    newstr = solveExp(r, dict, sub, leftTab, rightTab, lineTab, equTab)
    # logger.debug("newstr {}".format(newstr))
    return newstr

def findParanthese(r, dict, currentLine, leftTab, rightTab, lineTab, equTab):
    # logger.debug('str dans find paranthese {}'.format(currentLine))
    position1 = currentLine.find('(')
    if position1 == -1:
        return currentLine
    tmp = 1
    lenght = len(currentLine)
    i = position1 + 1
    position2 = 0
    while(i < lenght):
        if currentLine[i] == '(':
            tmp += 1
        elif currentLine[i] == ')' and tmp == 1:
            position2 = i
            break
        elif currentLine[i] == ')' and tmp != 1:
            tmp -= 1
        i += 1
    # logger.debug("position2 {}".format(position2))
    sub = currentLine[position1+1:position2]
    # logger.debug("sub  {}".format(sub))
    ret = solveExp(r, dict, sub, leftTab, rightTab, lineTab, equTab)
    newstr = currentLine.replace("("+sub+")", ret, 1)
    # logger.debug("printstr {}".format(newstr))
    return newstr
