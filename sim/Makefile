TEST_MODULE?=ahb_axi4

ifeq ($(OS),Windows_NT)
	RM_CMD = powershell if (Test-Path $(TEST_MODULE)) { Remove-Item -Recurse -Force -ErrorAction SilentlyContinue $(TEST_MODULE) }
else
	RM_CMD = rm -rf $(TEST_MODULE)
endif

all: run_sim

run_sim:
	qrun -64 -verbose -lint=default -parallel -vlog.sv -vopt.access=rw+/. -f rtl.f -f tb.f -top $(TEST_MODULE)_tb -outdir $(TEST_MODULE) -l $(TEST_MODULE)/qrun.log -designfile $(TEST_MODULE)/$(TEST_MODULE).bin -qwavedb=+memory=all+signal+class+wavefile=$(TEST_MODULE)/$(TEST_MODULE).db

clean:
	$(RM_CMD)

# .PHONY: all clean