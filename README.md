# smt-switch
An API for SMT solving with various solvers. This is a work in progress and there's still lots to be done.

# Current Solvers
Currently supports some features of CVC4, Z3 and Boolector

# Getting Started
Because smt-switch requries python3, a virtualenv is recommended.
* [virtualenv](https://virtualenv.pypa.io/en/stable/installation/)
* [virtualenvwrapper](http://virtualenvwrapper.readthedocs.io/en/latest/install.html)

After installing virtualenv and virtualenvwrapper, create an environment with ```mkvirtualenv <venv_name> --python=python3```.
You can setup your virtualenv to add the SMT solvers to your PYTHONPATH automatically by modifying <virtualenv directory>/<venv name>/bin/postactivate
Then, use this virtualenv whenever you use smt-switch.

See demo.py for an introduction. There are more examples in smt_switch/tests
