
from lark import Lark, Transformer
import sys, os


# Usage from commandshell
# comment out last line
#    parseFile(simpleExample2)
# python3 parser_step2.py <input_file>
#   where <input_file> is the human readable output of the new proof format
#   generated e.g. by
#   ~/Dropbox/otherlanguages/Z3/creatingProofLogs/vers12/
#   or
#   ~/Dropbox/otherlanguages/Z3/creatingProofLogs/vers11/

exampleFile="/home/csetzer/Dropbox/otherlanguages/Z3/rupNewFormatParser/program/vers1-initialParsing/anton_tseitinExample11-prooflog.txt"
simpleExample2="/home/csetzer/Dropbox/otherlanguages/Z3/rupNewFormatParser/program/vers1-initialParsing/simpleExample2.txt"

testAgdaFileName="/home/csetzer/Dropbox/otherlanguages/Z3/rupNewFormatParser/program/vers1-initialParsing/test.agda"

agdaHeaderFileName="/home/csetzer/Dropbox/otherlanguages/Z3/rupNewFormatParser/program/vers1-initialParsing/header.agda"
agdaFooterFileName="/home/csetzer/Dropbox/otherlanguages/Z3/rupNewFormatParser/program/vers1-initialParsing/footer.agda"

grammar = r"""
    start: item+

    item: "tseitin" "(" formula_list ")" "[" "]" "[" formula_list "]"   -> tseitin_item
        | "assumption" "[" "]" "[" formula_list "]"                     -> assumption_item
        | "rup" "[" "]" "[" formula_list "]"                            -> rup_item

    formula_list: (formula ("," formula)*)?

    formula: "True"        -> true_const
           | "False"       -> false_const
           | ATOM          -> atom
           | "Not" "(" formula ")"        -> not_formula
           | "Implies" "(" formula "," formula ")" -> imp_formula
           | "And" "(" formula ("," formula)* ")" -> and_formula
           | "Or" "(" formula ("," formula)* ")"  -> or_formula

    ATOM: /[a-zA-Z0-9_]+/

    %import common.WS
    %ignore WS
"""

def convert_prooflog_filename(input_filepath: str) -> str:
    # Based on code created by gemini
    """
    Converts a filename from '<file>-prooflog.txt' to '<file>-proofCheck.agda'.

    Args:
        input_filepath (str): The original file path, e.g., 'path/to/my-file-prooflog.txt'.

    Returns:
        str: The new file path, e.g., 'path/to/my-file-proofCheck.agda'.
    """
    # Split the path into directory and filename
    directory, filename = os.path.split(input_filepath)

    # Split the filename into base name and extension
    # e.g., "my-file-prooflog.txt" -> ("my-file-prooflog", ".txt")
    base_name, old_extension = os.path.splitext(filename)

    # Perform the generic replacement on the base name
    # This handles cases where "prooflog" might not be at the very end
    # but assumes the pattern "-prooflog" is what defines the part to change.
    new_base_name = base_name.replace("-prooflog", "-proofCheck")

    # Construct the new filename with the desired extension
    new_filename = new_base_name + ".agda"

    # Join the directory back with the new filename
    return os.path.join(directory, new_filename)

def label(f):
    return f[0]

def equal_formulas(f1, f2):
    if isinstance(f1, tuple) and isinstance(f2, tuple):
        if label(f1) != label(f2):
            return False
        return all(equal_formulas(a, b) for a, b in zip(f1[1:], f2[1:]))
    return f1 == f2

def equal_ListFormulas(f1, f2):
    return len(f1) == len(f2) and all(equal_formulas(x,y) for x,y in zip(f1,f2))

# f1 and f2 have the same elements
def equivalent_ListFormulas(f1, f2):
    if len(f1) != len(f2):
        return False
    else:
        subset1 = all( (any(equal_formulas(x,y) for y in f2) for x in f1))
        subset2 = all( (any(equal_formulas(x,y) for y in f1) for x in f2))
        return subset1 and subset2

# f1 has the negation of all elements in f2 and vice versa
def equivalentNeg_ListFormulas(f1, f2):
    if len(f1) != len(f2):
        return False
    else:
        subset1 = all( (any(equal_formulas(Neg(x),y) for y in f2) for x in f1))
        subset2 = all( (any(equal_formulas(Neg(x),y) for y in f1) for x in f2))
        return subset1 and subset2

# elements in f1 are the negation of elements in f2
def equal_NegListFormulas(f1, f2):
    return len(f1) == len(f2) and all(equal_formulas(Neg(x),y) for x,y in zip(f1,f2))


def formulaToAgda(f):
    if isinstance(f, tuple):
        if MatchesTrue(f):
            return ("trueFor")
        elif MatchesFalse(f):
            return ("falseFor")
        elif MatchesNot(f):
            return ("(notFor " + formulaToAgda(notChild(f)) + ")")
        elif MatchesImp(f):
            return ("(impFor " + formulaToAgda(impChild1(f)) + " " + formulaToAgda(impChild2(f)) + " )")
        elif MatchesAnd(f):
            return("(andFor " + formulaListToAgda(andChildList(f)) + " )")
        elif MatchesOr(f):
            return("(orFor " + formulaListToAgda(andChildList(f)) + " )")
        else:
            raise ConversionToAgdaError(f)
    else:
        return ('(zvar "' + f +  '" )')

def parsedItemsToAgdaContent(parsedItems,agdaFileName=testAgdaFileName):
    agdaHeader = open(agdaHeaderFileName,"r")
    file=open(agdaFileName,"w")
    for line in agdaHeader:
        file.write(line)
    agdaHeader.close()
    parsedItems.reverse()
    for line in parsedItems:
        if isinstance(line, tuple):
            label = line[0]
            if label== "tseitinImpElim":
                file.write("  (tseitinImpElim "+  formulaToAgda(line[1]) + " " \
                           + formulaToAgda(line[2]) + " ) ∷ \n")
            elif label== "tseitinImpIntro1":
                file.write("  (tseitinImpIntro1 "+  formulaToAgda(line[1]) + " " \
                           + formulaToAgda(line[2]) + " ) ∷ \n")
            elif label== "tseitinImpIntro2":
                file.write("  (tseitinImpIntro2 "+  formulaToAgda(line[1]) + " " \
                           + formulaToAgda(line[2]) + " ) ∷ \n")
            elif label== "tseitinImpIntro3":
                file.write("  (tseitinImpIntro3 "+  formulaToAgda(line[1]) + " " \
                           + formulaToAgda(line[2]) + " ) ∷ \n")
            elif label== "tseitinNot":
                file.write("  (tseitinNot "+  formulaToAgda(line[1]) + " ) ∷ \n")
            elif label== "tseitinAndElim":
                file.write("  (tseitinAndElim "+  formulaListToAgda(line[1]) + \
                           " " + str(line[2]) + " ) ∷ \n")
            elif label== "tseitinAndIntro":
                file.write("  (tseitinAndIntro "+  formulaListToAgda(line[1]) + \
                           " ) ∷ \n")
            elif label== "tseitinOrIntro":
                file.write("  (tseitinOrIntro "+  formulaListToAgda(line[1]) + \
                           " " + str(line[2]) + " ) ∷ \n")
            elif label== "tseitinOrElim":
                file.write("  (tseitinOrElim "+  formulaListToAgda(line[1]) + \
                           " ) ∷ \n")
            elif label== "assumption":
                file.write("  (assumptionZ3 "+  formulaListToAgda(line[1]) + \
                           " ) ∷ \n")
            elif label== "rup":
                file.write("  (rupZ3proof "+  formulaListToAgda(line[1]) + \
                           " ) ∷ \n")
            else:
                print("ERROR in fromulaToAgda - Item not found")
    file.write("  []")
    agdaFooter = open(agdaFooterFileName,"r")
    for line in agdaFooter:
        file.write(line)
    agdaHeader.close()
    file.close()

import os



def formulaListToAgda(f):
    # print("f=",f)
    result = "("
    for x in f:
        result = result + formulaToAgda(x) + " ∷ "
    return result + "[])"


def Neg(f):
    if isinstance(f, tuple) and f[0] == "Not":
        return f[1]
    return ("Not", f)

def Not(f):
    return ("Not", f)

def MatchesTrue(f):
    return isinstance(f,tuple) and f[0]== "True" and len(f) == 1

def MatchesFalse(f):
    return isinstance(f,tuple) and f[0]== "False" and len(f) == 1

def MatchesNot(f):
    return isinstance(f,tuple) and f[0]== "Not" and len(f) == 2

def notChild (f):
    return f[1]

def MatchesImp(f):
    return isinstance(f,tuple) and f[0]== "Implies" and len(f) == 3

def impChild1 (f):
    return f[1]

def impChild2 (f):
    return f[2]

def MatchesAnd(f):
    return isinstance(f,tuple) and f[0]== "And"

def andLength (f):
    return len(f[1])

def andChild (f,i):
    return f[1][i]

def andChildList (f):
    return f[1]


def MatchesOr(f):
    return isinstance(f,tuple) and f[0]== "Or"

def orLength (f):
    return f[1][i]

def orChild (f,i):
    return f[1][i]

def orChildList (f):
    return f[1]


def tseitinChecker(f_list,g_list):
    if len(f_list)< 2 or len(g_list) < 2:
        result = "ERROR len(f_list)< 2 or len(g_list) < 2"
        #print(result)
        return result


    # Case 1
    # tseitin(Not(Implies(a, b)), Neg(a), b) [] [Neg(a), b, Not(Implies(a, b))]
    # f-list = [ Not(Implies(a, b)), Neg(a), b ]
    # g-list = [ Neg(a), b, Not(Implies(a, b))]
    #
    # Output of parser: tseitinImpElim(a,b)

    if len(f_list) == 3 and len(g_list) == 3 and MatchesNot(f_list[0]) \
             and MatchesImp(notChild(f_list[0])):
        a = impChild1(notChild(f_list[0]))
        b = impChild2(notChild(f_list[0]))
        # print("a=",a)
        # print("b=",b)
        if equal_formulas(f_list[1],Neg(a)) and equal_formulas(f_list[2],b) and\
           equal_formulas(g_list[0],f_list[1]) and equal_formulas(g_list[1],f_list[2]) and\
           equal_formulas(g_list[2],f_list[0]):
            result = ("tseitinImpElim",a,b)
            #print ("Success, result = ",result)
            return True,result

    # Case 2
    # tseitin(a, Implies(a, b)) [] [a, Implies(a, b)]
    # f-list = [a, Implies(a, b)]
    # g-list =[a, Implies(a, b)]
    # Output of parser: tseitinImpIntro(a,b)

    if len(f_list) == 2 and len(g_list) == 2 and MatchesImp(f_list[1]):
        # print("Trying tseitinImpIntro1")
        a = impChild1(f_list[1])
        b = impChild2(f_list[1])
        # print("a=",a)
        # print("b=",b)
        if equal_formulas(f_list[0],a) and \
           equal_formulas(g_list[0],f_list[0]) and equal_formulas(g_list[1],f_list[1]):
            result = ("tseitinImpIntro1",a,b)
            #print ("Success, result = ",result)
            return True,result
        # print("End tseitinImpIntro1")

    # Case 3
    # tseitin(Neg(b), Implies(a, b)) [] [Neg(b), Implies(a, b)]
    # f-list = [Neg(b), Implies(a, b)]
    # g-list =[Neg(b), Implies(a, b)]
    #
    # Output of parser: tseitinImpIntro2(a,b)

    if len(f_list) == 2 and len(g_list) == 2 and MatchesImp(f_list[1]):
        # print("Trying tseitinImpIntro2")
        a = impChild1(f_list[1])
        b = impChild2(f_list[1])
        # print("a=",a)
        # print("b=",b)
        if equal_formulas(f_list[0],Neg(b)) and \
           equal_formulas(g_list[0],f_list[0]) and equal_formulas(g_list[1],f_list[1]):
            result = ("tseitinImpIntro2",a,b)
            #print ("Success, result = ",result)
            return True,result

    # Special case, Occurred in anton_tseitinExample9-prooflog.txt
    #    difference is Neg(b) vs Not(b)
    #
    # tseitin(Neg(b), Implies(a, b)) [] [Not(b), Implies(a, b)]
    # f-list = [Neg(b), Implies(a, b)]
    # g-list =[Not(b), Implies(a, b)]
    #
    # Output of parser: tseitinImpIntro2(a,b)

    if len(f_list) == 2 and len(g_list) == 2 and MatchesImp(f_list[1]):
        # print("Trying tseitinImpIntro3")
        a = impChild1(f_list[1])
        b = impChild2(f_list[1])
        # print("a=",a)
        # print("b=",b)
        if equal_formulas(f_list[0],Neg(b)) and \
           equal_formulas(g_list[0],Not(b)) and equal_formulas(g_list[1],f_list[1]):
            result = ("tseitinImpIntro3",a,b)
            #print ("Success, result = ",result)
            return True,result

    # Case 4
    # tseitin(b, Not(b)) [] [b, Not(Not(Neg(b)))]
    # f-list = [b, Not(b)]
    # g-list = [b, Not(Not(Neg(b)))]
    #
    # Output of parser: tseitinNot(b)

    if len(f_list) == 2 and len(g_list) == 2 and MatchesNot(f_list[1]):
        # print("Trying tseitinNot")
        b = f_list[0]
        # print("a=",a)
        if equal_formulas(f_list[1],Not(b)) and \
           equal_formulas(g_list[0],b) and equal_formulas(g_list[1],Not(Not(Neg(b)))):
            result = ("tseitinNot",b)
            #print ("Success, result = ",result)
            return True,result

    # Case 5
    # tseitin(Not(And(a1, .. , an)),  ai) [] [ai , Not(And(a1 , .. , an))]
    #
    # f-list = [Not(And(a1, .. , an)),  ai]
    # g-list =[ai , Not(And(a1 , .. , an))]
    #
    # Output of parser:
    # AndElim(i,[a1,..,an])
    if len(f_list) == 2 and len(g_list) == 2 and MatchesNot(f_list[0])\
       and MatchesAnd(notChild(f_list[0])) and equal_formulas(f_list[0],g_list[1])\
       and equal_formulas(f_list[1],g_list[0]):
        # print("Trying tseitinAndElim")
        aList = andChildList(notChild(f_list[0]))
        b = f_list[1]
        for i in range(len(aList)):
            if equal_formulas(aList[i],b):
                result = ("tseitinAndElim",aList,i)
                #print ("Success, result = ",result)
                return True,result


    # Case 6
    # tseitin(Neg(a1), ... , Neg(an), And(a1, .. , an)) [] [ Neg(a1) , .. , Neg(an), And(a1, .. , an)]
    # f-list = [Neg(a1), ... , Neg(an), And(a1, .. , an)]
    # g-list =[Neg(a1) , .. , Neg(an), And(a1, .. , an)]
    #
    #
    # Output of parser:
    # tseitinAndIntro([a1,..,an])

    if len(f_list) >= 2 and MatchesAnd(f_list[-1])\
       and equal_NegListFormulas(f_list[:-1],andChildList(f_list[-1]))\
       and equivalent_ListFormulas(f_list,g_list):
        aList = andChildList(f_list[-1])
        result = ("tseitinAndIntro",aList)
        #print ("Success, result = ",result)
        return True,result

    # Case 7
    # tseitin(Neg(ai), Or(a1 , .. , an)) [] [Neg(ai), Or(a1 , .. , an)]
    # f-list = [Neg(ai), Or(a1 , .. , an)]
    # g-list =[Neg(ai), Or(a1 , .. , an)]
    #
    # Output of parser:
    # tseitinOrIntro(i,[a1,..,an])


    if len(f_list) == 2 and len(g_list) == 2 and MatchesOr(f_list[1])\
       and equal_formulas(f_list[0],g_list[0])\
       and equal_formulas(f_list[1],g_list[1]):
        # print("Trying tseitinAndElim")
        aList = orChildList(f_list[1])
        b = f_list[0]
        for i in range(len(aList)):
            if equal_formulas(b,Neg(aList[i])):
                result = ("tseitinOrIntro",aList,i)
                # print ("Success, result = ",result)
                return True,result

    # Case 8
    # tseitin(a1 , .. , an,  Not(Or(a1, .., an))) [] [a1 , .. an, Not(Or(a1 , ... , an))]
    #
    # f-list = [a1 , .. , an,  Not(Or(a1, .., an))]
    # g-list =[a1 , .. an, Not(Or(a1 , ... , an))]
    #
    # Output of parser:
    # tseitinOrElim([a1,..,an])

    if len(f_list) >= 2 and MatchesNot(f_list[-1])\
       and MatchesOr(notChild(f_list[-1]))\
       and equal_ListFormulas(f_list[:-1],orChildList(notChild(f_list[-1])))\
       and equal_ListFormulas(f_list,g_list):
        aList = orChildList(notChild(f_list[-1]))
        result = ("tseitinOrElim",aList)
        # print ("Success, result = ",result)
        return True,result


    else:
        result = "ERROR"
        return False,result

class FormulaTransformer(Transformer):
    def __init__(self):
        self.parsed_items = []


    def tseitin_item(self, items):
        f_list = items[0]
        g_list = items[1]

        # print("tseitinCheck")
        # print("Formulas f:", f_list)
        # print("Formulas g:", g_list)

        success,result = tseitinChecker(f_list,g_list)
        if success:
            self.parsed_items.append(result)
        else:
            print("ERROR")
            print("Formulas f=", f_list)
            print("Formulas g=", g_list)
            self.parsed_items.append(result)

    def assumption_item(self, items):
        # print("assumption")
        # print("Formulas:", items[0])
        self.parsed_items.append(("assumption", items[0]))

    def rup_item(self, items):
        # print("rup")
        # print("Formulas:", items[0])
        self.parsed_items.append(("rup", items[0]))

    def formula_list(self, items):
        return items

    def atom(self, items):
        return str(items[0])

    def true_const(self, _):
        return ("True",)

    def false_const(self, _):
        return ("False",)

    def not_formula(self, items):
        return ("Not", items[0])

    def imp_formula(self, items):
        return ("Implies", items[0], items[1])

    def and_formula(self, items):
        return ("And", [*items])

    def or_formula(self, items):
        return ("Or", [*items])

def parseFile(fileName,agdaFileName=testAgdaFileName):
    # print("Starting")
    with open(fileName, 'r') as file:
        input_text = file.read()

    parser = Lark(grammar, start='start', parser='lalr')
    tree = parser.parse(input_text)

    transformer = FormulaTransformer()
    transformer.transform(tree)

    parsedItemsToAgdaContent(transformer.parsed_items,agdaFileName=agdaFileName)

    print("\nParsed Items:")
    for item in transformer.parsed_items:
        print(item)
    return transformer.parsed_items

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python parser_step2.py <input_file>")
        sys.exit(1)
    else:
        filename1 =sys.argv[1]
        parseFile(filename1,convert_prooflog_filename(filename1))

# parseFile(simpleExample2)
