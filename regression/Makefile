TESTS=$(basename $(sort $(wildcard test*.expr)))

RC=../src/rc.opt

.PHONY: check $(TESTS) 

check: $(TESTS)

$(TESTS): %: %.expr
	@echo "Testing interpreter"
	@cat $@.input | $(RC) -i $< > $@.log && diff $@.log orig/$@.log
	@echo "Testing SM"
	@cat $@.input | $(RC) -s $< > $@.log && diff $@.log orig/$@.log
	@echo "Testing asm"
	@$(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log

clean:
	rm -f test*.log *.s *~ $(TESTS)
	find ./ deep-expressions/ expressions/ -type f \( -name "generated*" -or -name "test*" \) -and ! -name "*.*" -exec rm {} \;
