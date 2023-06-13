# Running 'make labN' should cause the compiler for labN to be placed
# in the bin directory as bin/c0c. You can add to this makefile or
# change the default behavior from lab1 to lab2 (and so on) as you
# progress through the course. Don't change the behavior of 'make
# labN' or 'make clean'.

.PHONY: lab*  

default: src
	$(MAKE) -C src
src: bin
	$(MAKE) -C src

bin:
	mkdir bin

clean:
	rm -Rf bin
	for l in lab*; do $(MAKE) -C $$l clean; done

test:
	./gradecompiler  -q --autograder   ./l6-tests
