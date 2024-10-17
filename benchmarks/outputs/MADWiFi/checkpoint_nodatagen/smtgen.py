'''
SMTGen is a comiler that compiles a list of invariants to a 
runnable SMTLib query file that can be used to check the invariants'
relationship.
'''
import re
import tempfile
import sys
from typing import List
from enum import Enum
from dataclasses import dataclass

class TokenType(Enum):
    POW = 1
    MUL = 2
    PLUS = 3
    MINUS = 4
    DIVIDE = 5
    MODULO = 6
    ATOM = 7
    NUMBER = 8
    UNDERSCORE = 9
    LPAREN = 10
    RPAREN = 11
    COMMA = 12

    EQ = 13
    LT = 14
    GT = 15
    LTE = 16
    GTE = 17

    KW_MAX = 18
    KW_MIN = 19
    KW_MOD = 20


class Token:
    def __init__(self, _type: TokenType, value: str):
        self.value = value
        self.type = _type

    def __repr__(self):
        return f"{self.type}({self.value})"

    def __str__(self):
        return f"{self.value}"


# Define regular expressions for each token type
TOKEN_REGEX = {
    TokenType.POW: r"\*\*",
    TokenType.MUL: r"\*",
    TokenType.PLUS: r"\+",
    TokenType.MINUS: r"-",
    TokenType.MODULO: r"%",
    TokenType.DIVIDE: r"/",
    TokenType.EQ: r"==",
    TokenType.LT: r"<",
    TokenType.GT: r">",
    TokenType.LTE: r"<=",
    TokenType.GTE: r">=",
    TokenType.COMMA: r",",
    TokenType.UNDERSCORE: r"_",
    TokenType.LPAREN: r"\(",
    TokenType.RPAREN: r"\)",
    TokenType.NUMBER: r"\d+",
    TokenType.ATOM: r"[a-zA-Z_][a-zA-Z0-9_]*",
}

PRECEDENCE_MAP = {
    TokenType.POW: 50,
    TokenType.MUL: 40,
    TokenType.DIVIDE: 40,
    TokenType.PLUS: 30,
    TokenType.MINUS: 30,
    TokenType.MODULO: 20,  # This goes to the end for our case, even though in
    # Python's precedence, it is not.
}

# Define keywords
KEYWORDS = {"max": TokenType.KW_MAX, "mod": TokenType.KW_MOD, "min": TokenType.KW_MIN}


def lexer(input_string) -> List[Token]:
    tokens = []
    i = 0

    match = None
    while i < len(input_string):
        # Skip all whitespaces.
        if input_string[i] == " ":
            i += 1
            continue

        match = None
        for token_type, regex in TOKEN_REGEX.items():
            # Try to match the input string starting at position i
            match = re.match(regex, input_string[i:])
            if match is not None:
                break

        # Found our first match. Move i to the new span length.
        if match is not None:
            value = match.group(0)
            i += len(value)

            # If the match is a keyword, convert it to the corresponding token type
            if value in KEYWORDS:
                tokens.append(Token(KEYWORDS[value], value))
            else:
                for token_type, regex in TOKEN_REGEX.items():
                    if regex == match.re.pattern:
                        tokens.append(Token(token_type, value))
                        break
        else:
            raise ValueError(f"Invalid token at position {i} as {input_string[i]}")

    return tokens


@dataclass
class UnaryExpr:
    operator: Token
    operand: "Expr"

    def __repr__(self):
        return f"(- {self.operand})"


@dataclass
class BinaryExpr:
    left: "Expr"
    operator: Token
    right: "Expr"

    def __repr__(self):
        operator_to_string = {
            TokenType.MUL: "*",
            TokenType.PLUS: "+",
            TokenType.MINUS: "-",
            TokenType.DIVIDE: "/",
            TokenType.POW: "pow",
        }
        return f"({operator_to_string[self.operator.type]} {self.left} {self.right})"


@dataclass
class Number:
    value: int

    def __repr__(self):
        return f"{self.value}"


@dataclass
class Atom:
    value: str

    def __repr__(self):
        return f"{self.value}"


@dataclass
class Max:
    args: List["Expr"]

    def __repr__(self):
        # check if we have more than 2 arguments, if so, we
        # need to generate the string recursively (as we will not have)
        # > 2 arguments in our smtlib max function.
        rval = f"(max2 {self.args[0]} {self.args[1]})"
        for arg in self.args[2:]:
            rval = f"(max2 {rval} {arg})"
        return rval
    
@dataclass
class Min:
    args: List["Expr"]
    
    def __repr__(self):
        rval = f"(min2 {self.args[0]} {self.args[1]})"
        for arg in self.args[2:]:
            rval = f"(min2 {rval} {arg})"
        return rval

@dataclass
class Mod:
    rem: "Expr"
    divisor: "Expr"


@dataclass
class Expr:
    def __repr__(self): ...


@dataclass
class ExprList:
    exprs: List[Expr]


def prattparser(input_tokens: List[Token], precedence: int = 0) -> Expr:
    # we always start with the LHS until we hit the equality operators,
    # The start symbols can be:
    # - atom
    # - number
    # - minus ( not unary, since we have expr, which becomes recursive again )
    # - max (keyword)
    # This is a single-token lookahead implementation as done in pratt parsing.
    # to remove effects of left-recursive grammar.
    if len(input_tokens) == 0:
        raise ValueError("Expected expression, got empty token stream")

    prefix = input_tokens.pop(0)

    unarymatch = False
    maxexpr = False
    minexpr = False

    if prefix.type == TokenType.NUMBER:
        prefix = Number(int(prefix.value))
    elif prefix.type == TokenType.ATOM:
        prefix = Atom(prefix.value)
    elif prefix.type == TokenType.MINUS:
        prefix = UnaryExpr(
            operator=prefix, operand=prattparser(input_tokens, precedence=100)
        )
    elif prefix.type == TokenType.KW_MAX:
        maxexpr = True
    elif prefix.type == TokenType.KW_MIN:
        minexpr = True
    elif prefix.type == TokenType.LPAREN:
        # We can immediately start to evaluate whatever is in this parenthesis
        # pair as an expression.
        return prattparser(input_tokens)
    elif prefix.type == TokenType.RPAREN:
        return prefix

    else:
        raise ValueError(
            f"Invariants cannot start with {prefix}; expected atom, number, - or max"
        )

    if unarymatch and len(input_tokens) == 0:
        raise ValueError("Expected expression after unary operator -")

    if maxexpr and len(input_tokens) == 0:
        raise ValueError("Expected expression list after max keyword")

    if len(input_tokens) == 0:
        return prefix

    while input_tokens:
        popped = input_tokens.pop(0)
        if popped.type in [
            TokenType.PLUS,
            TokenType.MINUS,
            TokenType.MUL,
            TokenType.DIVIDE,
            TokenType.POW,
        ]:

            op_precedence = PRECEDENCE_MAP[popped.type]
            if op_precedence > precedence:
                # Power has a slightly different precedence - successive powers should be
                # evaluated right to left.
                if popped.type == TokenType.POW:
                    right = prattparser(input_tokens, op_precedence - 1)
                else:
                    right = prattparser(input_tokens, op_precedence)
                prefix = BinaryExpr(left=prefix, operator=popped, right=right)
            else:
                input_tokens.insert(0, popped)
                return prefix

        elif popped.type == TokenType.LPAREN:
            if maxexpr or minexpr:
                # Parse the right into an expression, followed by a comma.
                exprs = [prattparser(input_tokens)]
                # check if start of input_tokens is a rparen.
                while input_tokens and not input_tokens[0].type == TokenType.RPAREN:
                    parsed = prattparser(input_tokens)
                    exprs.append(parsed)

                if maxexpr:
                    return Max(exprs)
                else:
                    return Min(exprs)

            else:
                # parse the "mod" keyword after that.
                checkmodkw = input_tokens.pop(0)
                if checkmodkw.type == TokenType.KW_MOD:
                    # parse the right expression after that.
                    right = prattparser(input_tokens)
                    return Mod(rem=prefix, divisor=right)
                else:
                    # Parse until we get a closing rparen, and return expr between that.
                    raise ValueError(
                        "Expected mod keyword after LPAREN. Prefix is: ", prefix
                    )

        elif popped.type == TokenType.COMMA:
            return prefix

    return prefix


class InvariantOperator(Enum):
    EQ = 1
    NEQ = 2
    LT = 3
    GT = 4
    LTE = 5
    GTE = 6
    MOD = 7


@dataclass
class Invariant:
    left: Expr
    operator: InvariantOperator
    right: Expr

    def __repr__(self):
        operator_to_string = {
            InvariantOperator.EQ: "=",
            InvariantOperator.NEQ: "!=",
            InvariantOperator.LT: "<",
            InvariantOperator.GT: ">",
            InvariantOperator.LTE: "<=",
            InvariantOperator.GTE: ">=",
        }
        if self.operator == InvariantOperator.MOD:
            # mod requires special handling.
            # we take whatever is the first part of the right (mod expr),
            # and generate a equal sexpr with equality instead, i.e.
            # if we have sth like x1 + x2 === 5 (mod 12), we generate
            # (= 12 (mod (+ x1 x2) 5))
            return f"(= {self.right.rem} (mod {self.left} {self.right.divisor}))"
        return f"({operator_to_string[self.operator]} {self.left} {self.right})"


def invgen(invariant_string: str) -> (List[Token], Invariant):
    """
    Generates an invariant expression from a string, and returns all atoms found.
    We use these atoms to generate function definitions later.
    """
    invariant_operators = {
        "===": InvariantOperator.MOD,
        "==": InvariantOperator.EQ,
        "!=": InvariantOperator.NEQ,
        "<=": InvariantOperator.LTE,
        ">=": InvariantOperator.GTE,
        "<": InvariantOperator.LT,
        ">": InvariantOperator.GT,
    }

    for key in invariant_operators.keys():
        if key in invariant_string:
            left, right = invariant_string.split(key)
            leftatoms = [token for token in lexer(left) if token.type == TokenType.ATOM]
            rightatoms = [
                token for token in lexer(right) if token.type == TokenType.ATOM
            ]

            return leftatoms + rightatoms, Invariant(
                prattparser(lexer(left)),
                invariant_operators[key],
                prattparser(lexer(right)),
            )


# main exported function
def invariant_to_s_expr(invariant: str) -> (List[str], str):
    rval = invgen(invariant)
    return list(set(str(tok) for tok in rval[0])), str(rval[1])


def generate_invariants_conjunction(invariants: List[str]) -> (List[str], str):
    """
    Generates a conjunction of invariants from a list of strings.
    """
    rval = []
    atoms = set()
    for inv in invariants:
        rval.append(invariant_to_s_expr(inv)[1])
        for atom in invariant_to_s_expr(inv)[0]:
            atoms.add(atom)

    # No need to do conjunction if only one inequality in the invariant.
    if len(rval) == 1:
        return atoms, rval[0]

    if len(rval) == 0:
        return atoms, "true"

    sb = "(and "
    for inv in rval:
        sb += inv
    sb += ")"
    return atoms, sb


def generate_smtlib(variables, ours, evo):
    spaced_vars = " ".join(variables)
    varlist = ""
    for var in variables:
        varlist += f" ({var} Int) "

    template = f"""
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ({varlist}) Bool {ours}) 
(define-fun evo ({varlist}) Bool {evo})

(push)
(assert (forall ({varlist}) (=> (ours {spaced_vars}) (evo {spaced_vars}) )))
(check-sat)
(pop)

(push)
(assert (forall ({varlist}) (=> (evo {spaced_vars}) (ours {spaced_vars}) )))
(check-sat)
(pop)
    """

    return template

def generate_smtlibqueryfile_from_files(file1, file2):
    '''
    Given two files, which contain a list of invariants, like
    
    file1:
    a<b
    -a > -b
    
    file2:
    a == b
    a + 1 == c
    
    it generates a single smtlib query file, with contents like:
    
    ...
    (define-fun file1 ((.. vars list ..)) Bool (and (< a b) (> -a -b)))
    (define-fun file2 ((.. vars list ..)) Bool (and (= a b) (= (+ a 1) c)))
    ...
    .. push, pop, check-sat on each ..
    
    which can be used to check if the two files contain the same set of invariants.
    '''
    
    # Read file1 line by line, and convert it to a list of invariants.
    invs1_raw = []
    invs2_raw = []
    
    with open(file1, "r") as f:
        invs1_raw = f.readlines()
        
    print(f"Raw invariants: #{invs1_raw}#")
    
    with open(file2, "r") as f:
        invs2_raw = f.readlines()
   
    print(f"Raw invariants: #{invs2_raw}#")
    
    variables = set()
    invariants_1 = []
    invariants_2 = []
     
    for inv_raw in invs1_raw:
        this_vars, invariants = invariant_to_s_expr(inv_raw)
        variables.update(this_vars)
        invariants_1.append(invariants)
    
    for inv_raw in invs2_raw:
        this_vars, invariants = invariant_to_s_expr(inv_raw)
        variables.update(this_vars)
        invariants_2.append(invariants)
    
    ourvars, ours = generate_invariants_conjunction(invariants_1)
    evovars, evos = generate_invariants_conjunction(invariants_2)
    
    variables.update(ourvars)
    variables.update(evovars) 
     
    smtlib_content = generate_smtlib(variables, ours, evos)

    # TODO: This is a hack, we should not be writing to a file on /tmp.
    with open("/tmp/temp-smtlib-file", "w") as f:
        f.write(smtlib_content)
        return f.name
    

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python smtgen.py <file1> <file2>")
        sys.exit(1)
        
    file1 = sys.argv[1]
    file2 = sys.argv[2]
    
    print(generate_smtlibqueryfile_from_files(file1, file2))