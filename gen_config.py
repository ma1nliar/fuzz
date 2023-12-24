from fuzzingbook.Grammars import crange, srange, convert_ebnf_grammar, extend_grammar, is_valid_grammar
from fuzzingbook.Grammars import START_SYMBOL, new_symbol, Grammar
from fuzzingbook.GrammarCoverageFuzzer import GrammarCoverageFuzzer
import os
import sys
import argparse
import random
import time

import json

BUILTIN_TYPES = {
    
}

def parse_grammar(filename: str) -> Grammar:
    data= {}
    with open(filename) as f:
        data = json.load(f)
    gram: Grammar = {}

    if data["bnf"]:
        gram = data
        del gram["bnf"]
    else:
        for k, v in BUILTIN_TYPES.items():
            gram[k] = v

        if "types" in data.keys():
            types = data["types"]
            for k, v in types.items():
                gram[k] = v

        opt_list = []

        for k, v in data["options"].items():
            opt_list.append(f"{k} {' '.join(v)}\n")
        gram["<start>"] = opt_list

    # print(gram)
    return gram

def gen_config(grammar: Grammar) -> str:
    if "min_nonterminals" in grammar.keys():
        min_nonterminals = grammar["min_nonterminals"]
        del grammar["min_nonterminals"]
    
    max_nonterminals = min_nonterminals + 5
    if "max_nonterminals" in grammar.keys():
        max_nonterminals = grammar["max_nonterminals"]
        del grammar["max_nonterminals"]

    assert is_valid_grammar(grammar)

    ebnf= convert_ebnf_grammar(grammar)

    f = GrammarCoverageFuzzer(ebnf, min_nonterminals = min_nonterminals, max_nonterminals = max_nonterminals)

    config = f.fuzz()

    # for i in range(len(grammar["<start>"])):
    #     config += f.fuzz()
    return config


def generate(grammar, symbol="<start>"):
    assert is_valid_grammar(grammar)

    if symbol not in grammar:
        return symbol
    else:
        expansion = random.choice(grammar[symbol])
        tokens = expansion.split()
        return " ".join(generate(grammar, token) for token in tokens)
    

def main(file):
    random.seed(time.time())

    grammar = parse_grammar(file)

    config = gen_config(grammar)
    # print(config)
    return config

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", metavar='json file', type=str, help="path of configuration definition file")
    parser.add_argument("--num", "-n", type=int, default=1, help="# of configuration files being generated")
    parser.add_argument("--dest", "-d", type=str, default=None, help="destination to save configuration files")
    parser.add_argument("--min_nonterminals", "-m", type=int, default=10, help="# of non-terminals")
    args = parser.parse_args()
    s = main(args.file)
    print(s)
    