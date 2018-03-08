# Installation Instructions

```
pip install -e .
```

# Verifying the build
## If you have all supported solvers installed, you can run
```
pip install pytest
pytest
```
As soon as I get a chance, I will check which solvers are installed so that pytest can be used with a subset of solvers.

## If you have a subset of the installed solvers
```
./demo.py <CVC4 | Boolector | Z3>
```