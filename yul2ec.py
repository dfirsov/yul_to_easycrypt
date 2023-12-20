import sys
import os
import json
import argparse
import re

from antlr4 import *
from tools.YulLexer import YulLexer 
from tools.YulParser import YulParser
from tools.YulListener import YulListener
from tools.YulEasyCryptListener import YulEasyCryptListener


# https://www.antlr3.org/api/Python/index.html
# https://github.com/jszheng/py3antlr4book/blob/master/08-JSON/json2xml.py
# https://github.com/antlr/antlr4/tree/dev/runtime/Python3
# https://www.rubydoc.info/gems/antlr4/0.9.2/RuleContext

def main():

    input_stream = FileStream(sys.argv[1])
    lexer = YulLexer(input_stream)
    token_stream = CommonTokenStream(lexer)
    parser = YulParser(token_stream)
    tree = parser.yul_object()
    printer = YulEasyCryptListener()
    walker = ParseTreeWalker()
    walker.walk(printer, tree)

    printer.ec_node.prepare()
    ec_code = printer.ec_node.to_str()

    print(ec_code)
    with open(sys.argv[2], 'w') as file:
        file.write(ec_code)

    print("Done.")


if __name__ == '__main__':
    main()
