#!/usr/bin/perl

use strict;
use warnings;
use autodie;

use List::Util qw(max);

# Process arguments
my( $N, $K ) = @ARGV;
$N //= 6;
$K //= 2**($N-2) + 1;
warn "Looking for convex $N-gons among $K points.\n";

# Initialize variables
my( $VARS, @CLAUSES, %var, %name, %desc );
$VARS = 0;
## A helper variable
clause( var( "true" ) );
## One "input" variable for each 3-tuple
for my $i (    1 .. $K ) {
for my $j ( $i+1 .. $K ) {
for my $k ( $j+1 .. $K ) {
	var( "in$i,$j,$k", "Is the triple of points $i-$j-$k convex up?" );
}
}
}
## Many "dynamic programming" variables
for my $s ( 1 .. $N-1 ) {
	for my $i (    1 .. $K ) {
	for my $j ( $i   .. $K ) {
	for my $k ( $j+1 .. $K ) {
		dp( "cap", $s, $i, $j, $k );
		dp( "cup", $s, $i, $j, $k );
	}
	}
	}
}

# Generate SAT instance

## Initial conditions for the dynamic programming are encoded through
## the dp(..) routine.

## Dynamic programming conditions
for my $s ( 2 .. $N-2 ) {
	my $t = $s+1;
	for my $i (    1 .. $K ) {
	for my $j ( $i   .. $K ) {
	for my $k ( $j+1 .. $K ) {
		### Extend the cap
		for my $l ( $k+1 .. $K ) {
			implies( dp( "cap", $s, $i, $j, $k ),
				 sat_not(var("in$j,$k,$l")),
				 dp( "cap", $t, $i, $k, $l )
				 );
		}
		### Extend the cup
		for my $l ( $k+1 .. $K ) {
			implies( dp( "cup", $s, $i, $j, $k ),
				 var("in$j,$k,$l"),
				 dp( "cup", $t, $i, $k, $l )
				 );
		}
	}
	}
	}
}
## Conditions on N-gons
for my $s1 ( 1 .. $N-1 ) {
	my $s2 = $N-$s1;
	for my $i  (    1 .. $K ) {
	for my $j1 ( $i   .. $K ) {
	for my $j2 ( $i   .. $K ) {
	for my $k  ( max($j1,$j2)+1 .. $K ) {
		clause( sat_not( dp( "cap", $s1, $i, $j1, $k ) ),
			sat_not( dp( "cup", $s2, $i, $j2, $k ) )
		      );
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
#	warn join( " ", map {name($_)} @$clause), "\n";
	print SAT_IN join " ", @$clause, "0\n";
}
close( SAT_IN );

my( $response, $result );
while( $response = <SAT_OUT> ) {
	last if $response =~ m/satisfiable/i;
}
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
		printf "%6d  %1s  %-15s %-40s\n", $var, ($assignment[$var] ? "1" : "0"), $name{$var}, $desc{$var};
	}
} else {
	print "Could not understand SAT solver response:\n$response";
}

# Subroutines
## Look up a variable by name, possibly adding a description in the process
sub var {
	my( $name, $desc ) = @_;
	if( not exists $var{$name} ) {
		my( $var );
		$VARS++;
		$var = $VARS;
		$var{$name} = $var;
		$desc = "" unless defined $desc;
		$desc{$var} = $desc;
		$name{$var} = $name;
	}
	return $var{$name};
}

## Look up a literal's name
sub name {
	my( $var ) = @_;
	return $name{$var} if $var > 0;
	return "-" . $name{0-$var};
}

## Negate a literal
sub sat_not {
	my( $var ) = @_;
	return -$var;
}

## Add a clause to the problem
sub clause {
	my( @vars ) = @_;
	push @CLAUSES, [@vars];
}

## dp( "cup", $s, $i, $j, $k ) represents whether there is a cup
## configuration of $s points starting at $i with final segment
## $j--$k, and similarly for "cap"
sub dp {
	my( $cupcap, $s, $i, $j, $k ) = @_;
	die "Unrecognized value cupcap=$cupcap.\n" unless $cupcap eq "cup" or $cupcap eq "cap";
	return var( "true" ) if $s == 1;
	return sat_not(var("true")) if $j <= $i;
	return var( "$cupcap$s,$i,$j,$k", "Is there a $cupcap $i..($j,$k) configuration of $s total points?" )
	  if $s > 2;
	die "Bad value of s=$s.\n" if $s != 2;
	if( $cupcap eq "cap" ) {
		return sat_not(var("in$i,$j,$k"));
	} else {
		return var("in$i,$j,$k");
	}
}

## implies( X, Y, Z, T ) adds a clause that X and Y and Z implies T,
## for any number of clauses X, Y, and Z, but always one clause T.
sub implies {
	my( @vars ) = @_;
	# Negate all of the variables except the last!
	for my $i ( 0 .. @vars-2 ) {
		$vars[$i] = sat_not($vars[$i]);
	}
	clause( @vars );
}
