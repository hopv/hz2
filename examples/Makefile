
PATH := $(CPDTPATH)

build:
	~/.opam/4.05.0/bin/coqc Hfl.v
	~/.opam/4.05.0/bin/coqc -R $(PATH) Cpdt HflTactics.v
