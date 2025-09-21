# 数学表达式解析器

数学表达式解析器，支持 `+`, `-`, `*`, `/`, `()` 运算，将表达式解析为抽象语法树并计算结果。

## 使用方法

```python
from parser import parse_expression_from_string
from calculator import eval_value

# 解析并计算表达式
ast1 = parse_expression_from_string("3 * 4 + 10 / 2")
print(f"Result: {eval_value(ast)}")
ast2 = parse_expression_from_file("expression.txt")
print(f"Parsed from file: {ast}")
print(f"Result: {eval_value(ast)}")
```

运行测试：`python parser.py`
