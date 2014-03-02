ccs-graph
=========

ccsTool.m is an implementation in Wolfram Mathematica of the following function.

getCcsGraph[process, definitions, iterationLimit] takes as input:
- process: a string that represents a CCS process
- definitions: a string that contains a sequence of semicolon separated CCS constant definition 
- iterationLimit: an upper limit to the iteration of the algorithm

It returns the semantic graph of the input process
