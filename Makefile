SOURCES = Binary.mli Binary.ml BinomialTree.mli BinomialTree.ml BinomialHeap.mli BinomialHeap.ml PriorityQueue.ml Graph.ml
RESULT = bh
ANNOTATE = true

all: dc dnc
	./bh

include OCamlMakefile
