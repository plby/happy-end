#!/usr/bin/perl

use strict;
use warnings;
use autodie;

# Process arguments
my( $N, $K ) = @ARGV;
$N //= 6;
$K //= 2**($N-2) + 1;

# Initialize variables
my( $VARS, %var, %name );
$VARS = 0;

# Generate SAT instance


# Subroutines
sub var {
	my( $name ) = @_;
	if( not exists $var{$name} ) {
		$VARS++;
		$var{$name} = $VARS;
		$name{$VARS} = $name;
	}
	return $var{$name};
}
