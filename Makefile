.PHONY: all clean

all: 
	$(MAKE) -C theories
	$(MAKE) -C tools
	$(MAKE) -C tools/example

clean: 
	$(MAKE) -C theories clean
	$(MAKE) -C tools clean 
	$(MAKE) -C tools/example clean
