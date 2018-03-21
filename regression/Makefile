TESTS=$(basename $(sort $(wildcard test*.expr)))

RC=../src/rc.opt

.PHONY: check $(TESTS) 

check: $(TESTS)

$(TESTS): %: %.expr
<<<<<<< HEAD
	#@$(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
	cat $@.input | $(RC) -i $< > $@.log && diff $@.log orig/$@.log
	cat $@.input | $(RC) -s $< > $@.log && diff $@.log orig/$@.log
=======
	@echo 'testing expr eval'
	@cat $@.input | $(RC) -i $< > $@.log && diff $@.log orig/$@.log
	@echo 'testing SM eval'
	@cat $@.input | $(RC) -s $< > $@.log && diff $@.log orig/$@.log
	@echo 'testing asm'
	@$(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
>>>>>>> [HW1-HW8] Implement first 8 homeworks

clean:
	rm -f test*.log *.s *~ $(TESTS)
