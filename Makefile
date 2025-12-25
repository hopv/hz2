
build:
	dune build src/main.exe
	mv _build/default/src/main.exe hz2

clean:
	dune clean
