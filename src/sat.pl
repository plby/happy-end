#!/usr/bin/perl

use strict;
use warnings;
use autodie;

# Process arguments
my( $N, $K ) = @ARGV;
$N //= 6;
$K //= 2**($N-2) + 1;
warn "Looking for convex $N-gons among $K points.\n";

# Initialize variables
my( $VARS, @CLAUSES, %var, %name );
$VARS = 0;
## One "input" variable for each 3-tuple
for my $i (    1 .. $K ) {
for my $j ( $i+1 .. $K ) {
for my $k ( $j+1 .. $K ) {
	var( "in$i,$j,$k" );
}
}
}
## Many "dynamic programming" variables
for my $s ( 4 .. $N-1 ) {
for my $i (    1 .. $K ) {
for my $j ( $i+1 .. $K ) {
for my $k (    1 .. $K ) {
for my $l ( $k+1 .. $K ) {
	next if $i == $k or $i == $l or $j == $k or $j == $l;
	var( "dp$s;$i,$j;$k,$l" );
}
}
}
}
}
## A helper variable
clause( var( "true" ) );

# Generate SAT instance
## Four-point configurations follow from 3-point convexities and concavities
{
	my $s = 4;
	for my $i (    1 .. $K ) {
	for my $j ( $i+1 .. $K ) {
	for my $k (    1 .. $K ) {
	for my $l ( $k+1 .. $K ) {
		next if $i == $k or $i == $l or $j == $k or $j == $l;
		if( $i < $k ) {
		       	implies( sat_not(var("in$i,$k,$l")), var("dp$s;$i,$j;$k,$l") );
		} else {
		       	implies(         var("in$k,$i,$j") , var("dp$s;$i,$j;$k,$l") );
		}
	}
	}
	}
	}
}

# Interact with SAT solver
use IPC::Open3;
my( $solver, $pid, $CLAUSES );
$solver = "/usr/bin/picosat";
$pid = open3( \*SAT_IN, \*SAT_OUT, "", $solver );
$CLAUSES = 0+@CLAUSES;
warn "SAT problem has $VARS variables and $CLAUSES clauses.\n";
print SAT_IN "p cnf $VARS $CLAUSES\n";
for my $clause ( @CLAUSES ) {
	warn join( " ", map {name($_)} @$clause), "\n";
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
	print "A satisfiable assignment was found:\n";
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

sub name {
	my( $var ) = @_;
	return $name{$var} if $var > 0;
	return "-" . $name{0-$var};
}

sub sat_not {
	my( $var ) = @_;
	return -$var;
}

sub clause {
	my( @vars ) = @_;
	push @CLAUSES, [@vars];
}

sub implies {
	my( @vars ) = @_;
	# Negate all of the variables except the last!
	for my $i ( 0 .. @vars-2 ) {
		$vars[$i] = sat_not($vars[$i]);
	}
	clause( @vars );
}
