EXEC         = upal
EXAMPLES_DIR = examples
TESTS        = $(wildcard $(EXAMPLES_DIR)/*.ul)
TIMEOUT_SEC  = 1.5

.PHONY: all build test clean

all: build

build:
	@cabal build
	@cp $$(cabal list-bin $(EXEC)) ./$(EXEC)

test: build
	@for file in $(TESTS); do                                                                  \
	    echo "" ;                                                                              \
	    echo "**** $$file ****\n" ;                                                            \
	    TFILE=$$(mktemp) ;                                                                     \
	    OFILE=$$(mktemp) ;                                                                     \
	    ./$(EXEC) $$file hello world > $$OFILE 2>&1 &                                          \
	    PID=$$! ;                                                                              \
	    ( sleep $(TIMEOUT_SEC); if kill $$PID 2>/dev/null; then echo timeout > $$TFILE; fi ) & \
	    WATCHER=$$! ;                                                                          \
	    wait $$PID     2>/dev/null ;                                                           \
	    kill $$WATCHER 2>/dev/null ;                                                           \
	    wait $$WATCHER 2>/dev/null ;                                                           \
	    cat $$OFILE ;                                                                          \
	    if [ -s $$TFILE ]; then                                                                \
	        echo "[TIMEOUT] $$file execution exceeded $(TIMEOUT_SEC) seconds." ;               \
	    fi ;                                                                                   \
	    rm -f $$TFILE $$OFILE ;                                                                \
	done
	@echo ""
	@echo "Done."

clean:
	@cabal clean
	@rm -f $(EXEC)
	@rm -f *~ src/*~ examples/*~
