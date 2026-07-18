verPerl=perl-5.42.0@collector

build: clean
	perlbrew exec --with $(verPerl) bash -c '. $$HOME/.bashrc && pp --module Email::** --module Sys::Hostname --module Test::Pod --module Text::Unidecode --compile --tempcache $$(date +%s) -o collector.$$(uname -s) collector.pl'

clean:
	rm -f collector.$$(uname -s)

