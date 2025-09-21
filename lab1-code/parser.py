"""
Algebraic expression parser implementing lexical analysis and syntax parsing
Author: dahuangggg
"""

from typing import List, Union
from enum import Enum
from calculator import Expr, Num, Add, Minus, Multi, Div, Par


class TokenType(Enum):
    """Token types for mathematical expressions"""
    NUMBER = "NUMBER"
    PLUS = "PLUS"
    MINUS = "MINUS"
    MULTIPLY = "MULTIPLY"
    DIVIDE = "DIVIDE"
    LPAREN = "LPAREN"
    RPAREN = "RPAREN"
    EOF = "EOF"


class Token:
    """Represents a token with type, value, and position"""
    def __init__(self, type_: TokenType, value: Union[str, float], position: int):
        self.type = type_
        self.value = value
        self.position = position

    def __repr__(self):
        return f"Token({self.type}, {self.value}, {self.position})"


class Lexer:
    """Lexical analyzer that tokenizes mathematical expressions"""
    def __init__(self, text: str):
        self.text = text
        self.position = 0
        self.current_char = self.text[self.position] if self.position < len(self.text) else None

    def advance(self):
        """Move to next character in input"""
        self.position += 1
        if self.position >= len(self.text):
            self.current_char = None
        else:
            self.current_char = self.text[self.position]

    def skip_whitespace(self):
        """Skip whitespace characters"""
        while self.current_char is not None and self.current_char.isspace():
            self.advance()

    def read_number(self):
        """Read integer or float number"""
        num_str = ""
        start_pos = self.position

        while (self.current_char is not None and
               (self.current_char.isdigit() or self.current_char == '.')):
            num_str += self.current_char
            self.advance()

        if '.' in num_str:
            return Token(TokenType.NUMBER, float(num_str), start_pos)
        else:
            return Token(TokenType.NUMBER, int(num_str), start_pos)

    def get_next_token(self) -> Token:
        """Get next token from input"""
        while self.current_char is not None:
            if self.current_char.isspace():
                self.skip_whitespace()
                continue

            if self.current_char.isdigit():
                return self.read_number()

            if self.current_char == '+':
                token = Token(TokenType.PLUS, '+', self.position)
                self.advance()
                return token

            if self.current_char == '-':
                token = Token(TokenType.MINUS, '-', self.position)
                self.advance()
                return token

            if self.current_char == '*':
                token = Token(TokenType.MULTIPLY, '*', self.position)
                self.advance()
                return token

            if self.current_char == '/':
                token = Token(TokenType.DIVIDE, '/', self.position)
                self.advance()
                return token

            if self.current_char == '(':
                token = Token(TokenType.LPAREN, '(', self.position)
                self.advance()
                return token

            if self.current_char == ')':
                token = Token(TokenType.RPAREN, ')', self.position)
                self.advance()
                return token

            raise ValueError(f"Invalid character '{self.current_char}' at position {self.position}")

        return Token(TokenType.EOF, None, self.position)

    def tokenize(self) -> List[Token]:
        """Tokenize entire input string"""
        tokens = []
        while True:
            token = self.get_next_token()
            tokens.append(token)
            if token.type == TokenType.EOF:
                break
        return tokens


class Parser:
    """Recursive descent parser for mathematical expressions"""
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.position = 0
        self.current_token = self.tokens[0] if tokens else None

    def advance(self):
        """Move to next token"""
        self.position += 1
        if self.position < len(self.tokens):
            self.current_token = self.tokens[self.position]
        else:
            self.current_token = None

    def expect(self, token_type: TokenType):
        """Consume expected token type or raise error"""
        if self.current_token and self.current_token.type == token_type:
            token = self.current_token
            self.advance()
            return token
        else:
            expected = token_type.value
            actual = self.current_token.type.value if self.current_token else "EOF"
            raise ValueError(f"Expected {expected}, got {actual}")

    def parse(self) -> Expr:
        """Parse tokens into AST"""
        expr = self.parse_expression()
        if self.current_token and self.current_token.type != TokenType.EOF:
            raise ValueError(f"Unexpected token: {self.current_token}")
        return expr

    def parse_expression(self) -> Expr:
        """Parse addition and subtraction (lowest precedence)"""
        left = self.parse_term()

        while (self.current_token and
               self.current_token.type in [TokenType.PLUS, TokenType.MINUS]):
            op = self.current_token
            self.advance()
            right = self.parse_term()

            if op.type == TokenType.PLUS:
                left = Add(left, right)
            elif op.type == TokenType.MINUS:
                left = Minus(left, right)

        return left

    def parse_term(self) -> Expr:
        """Parse multiplication and division (higher precedence)"""
        left = self.parse_factor()

        while (self.current_token and
               self.current_token.type in [TokenType.MULTIPLY, TokenType.DIVIDE]):
            op = self.current_token
            self.advance()
            right = self.parse_factor()

            if op.type == TokenType.MULTIPLY:
                left = Multi(left, right)
            elif op.type == TokenType.DIVIDE:
                left = Div(left, right)

        return left

    def parse_factor(self) -> Expr:
        """Parse numbers and parenthesized expressions (highest precedence)"""
        if self.current_token.type == TokenType.NUMBER:
            value = self.current_token.value
            self.advance()
            return Num(value)

        elif self.current_token.type == TokenType.LPAREN:
            self.advance()
            expr = self.parse_expression()
            self.expect(TokenType.RPAREN)
            return Par(expr)

        else:
            raise ValueError(f"Unexpected token: {self.current_token}")


def parse_expression_from_string(expression: str) -> Expr:
    """Parse an algebraic expression string into an AST."""
    lexer = Lexer(expression)
    tokens = lexer.tokenize()
    parser = Parser(tokens)
    return parser.parse()


def parse_expression_from_file(filename: str) -> Expr:
    """Parse an algebraic expression from a file into an AST."""
    with open(filename, 'r') as file:
        expression = file.read().strip()
    return parse_expression_from_string(expression)


if __name__ == "__main__":
    """Test the parser with example expressions"""
    test_expressions = [
        "3 * 4 + 10 / 2",
        "(12 + 217) * 3 - 621",
        "2 + 3 * 4",
        "(1 + 2) * (3 + 4)",
    ]

    from calculator import eval_value

    for expr_str in test_expressions:
        print(f"Expression: {expr_str}")
        try:
            ast = parse_expression_from_string(expr_str)
            print(f"AST: {ast}")
            result = eval_value(ast)
            print(f"Result: {result}")
            print()
        except Exception as e:
            print(f"Error: {e}")
            print()
