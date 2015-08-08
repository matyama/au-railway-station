AU Railway Station
==================
Semestral project for Automatic Reasoning (A4M33AU) course (OI FEE CTU). Variant: ATP 

execution:
----------
- $ python3 sysgen.py [-p | --prove | -h | --help] path_to_example_dir
- e.g. $ python3 sysgen.py --prove examples/ex3

dependencies:
-------------
- python3
- pygraphpviz
- networkx

requirements:
-------------
- mace4
- prover9

experiments:
------------
1. examples/ex1 - very simple station with 4 nodes (1 input, 2 outputs, 1 switch)
2. examples/ex2 - small station with 6 nodes (2 inputs, 2 outputs, 2 switches, 4 paths)
3. examples/ex3 - medium station with 8 nodes (3 inputs, 2 outputs, 3 switches, 8 paths)
4. examples/ex4 - large station with 11 nodes (2 inputs, 3 outputs, 6 switches, 10 paths)
5. examples/ex5 - extra large station with 13 nodes (3 inputs, 3 outputs, 7 switches, 20 paths)
