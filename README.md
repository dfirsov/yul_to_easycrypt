# Yul to EasyCrypt transpiler

Work in progress: We implement a converter for a subset of Yul language to EasyCrypt module system.

# Setup

```
python3 -m venv yul2ec-env
source yul2ec-env/bin/activate
pip3 install antlr4-python3-runtime
pip3 install bigtree
```

# Running

`python3 yul2ec.py source.yul target.ec`
