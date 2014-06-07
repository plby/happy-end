#!/usr/bin/perl

use strict;
use warnings;
use autodie;

# Process arguments
my( $N, $K ) = @ARGV;
$N //= 6;
$K //= 2**($N-2) + 1;

# Initialize variables
my( $VARS, @CLAUSES, %var, %name );
$VARS = 0;
var( "x" );
var( "y" );
var( "z" );

# Generate SAT instance
clause( var("x"), var("y"), var("z") );
clause( sat_not(var("x")), sat_not(var("y")), sat_not(var("z")) );

# Interact with SAT solver
use IPC::Open3;
my( $solver, $pid );
$solver = "/usr/bin/picosat";
$pid = open3( \*SAT_IN, \*SAT_OUT, "", $solver );
print SAT_IN "p cnf $VARS ", 0+@CLAUSES, "\n";
for my $clause ( @CLAUSES ) {
	print SAT_IN join " ", @$clause, "0\n";
}
close( SAT_IN );

my( $response, $result );
$response = <SAT_OUT>;
if( $response =~ m/s unsatisfiable/i ) {
	print "Problem found unsatisfiable as desired.\n";
} elsif( $response =~ m/s satisfiable/i ) {
	my( @assignment );
	@assignment = ("") x $VARS;
	while( $response = <SAT_OUT> ) {
		while( $response =~ m/ (\d+)\b/g ) {
			$assignment[$1] = 1;
		}
	}
	print "Satisfiable assignment:\n";
	for my $var ( 1 .. $VARS ) {
		printf "%6d  %1s  %-20s\n", $var, ($assignment[$var] ? "1" : "0"), $name{$var};
	}
} else {
	print "Could not understand SAT solver response:\n$response";
}

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

sub sat_not {
	my( $var ) = @_;
	return -$var;
}

sub clause {
	my( @vars ) = @_;
	push @CLAUSES, [@vars];
}
