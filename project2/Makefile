.PHONY: test test1 test2 dist

Vsim: Vsim.c
	gcc -Wall -Werror -o $@ $<

test: test1 test2

test1: Vsim
	./Vsim sample.txt
	diff --color=auto simulation.txt sample_simulation.txt

test2: Vsim
	./Vsim test.txt
	diff --color=auto simulation.txt test_simulation.txt

dist: Vsim.c.txt

Vsim.c.txt: Vsim.c
	cp $< $@
