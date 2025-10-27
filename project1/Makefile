.PHONY: test dist

Vsim: Vsim.c
	gcc -Wall -Werror $< -o $@

test: Vsim
	./Vsim sample.txt
	diff --color=auto disassembly.txt sample_disassembly.txt
	diff --color=auto simulation.txt sample_simulation.txt
	./Vsim test.txt
	diff --color=auto disassembly.txt test_disassembly.txt
	diff --color=auto simulation.txt test_simulation.txt

dist: /tmp/Vsim.c.txt
/tmp/Vsim.c.txt: Vsim.c
	cp $< $@
