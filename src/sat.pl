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
## One "input" variable for each 3-tuple
for my $i (    1 .. $K ) {
for my $j ( $i+1 .. $K ) {
for my $k ( $j+1 .. $K ) {
	var( "in$i,$j,$k", "Is the triple of points $i-$j-$k convex up?" );
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
	dp( $s, $i, $j, $k, $l );
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
		       	implies( sat_not(var("in$i,$k,$l")), dp( $s, $i, $j, $k, $l ) );
		} else {
		       	implies(         var("in$k,$i,$j") , dp( $s, $i, $j, $k, $l ) );
		}
	}
	}
	}
	}
}
## Dynamic programming conditions
for my $s ( 4 .. $N-2 ) {
	my $t = $s+1;
	for my $i (    1 .. $K ) {
	for my $j ( $i+1 .. $K ) {
	for my $k (    1 .. $K ) {
	for my $l ( $k+1 .. $K ) {
		next if $i == $k or $i == $l or $j == $k or $j == $l;
		### Extend the cap
		for my $m ( $l+1 .. $K ) {
			next if $m == $i or $m == $j;
			implies( dp( $s, $i, $j, $k, $l ),
				 sat_not(var("in$k,$l,$m")),
				 dp( $t, $i, $j, $l, $m )
				 );
		}
		### Extend the cup
		for my $m ( $j+1 .. $K ) {
			next if $m == $k or $m == $l;
			implies( dp( $s, $i, $j, $k, $l ),
				 var("in$i,$j,$m"),
				 dp( $t, $j, $m, $k, $l )
				 );
		}
	}
	}
	}
	}
}
## Conditions on N-gons
{
	my $s = $N-1;
	for my $i (    1 .. $K ) {
	for my $j ( $i+1 .. $K ) {
	for my $k (    1 .. $K ) {
	for my $l ( $k+1 .. $K ) {
		next if $i == $k or $i == $l or $j == $k or $j == $l;
		### Usual closing configuration
		for my $m ( max($j,$l)+1 .. $K ) {
			implies( dp( $s, $i, $j, $k, $l ),
				 var("in$i,$j,$m"),
				 sat_not(var("in$k,$l,$m")),
				 sat_not(var("true")) # ie, the antecedent is false
			       );
		}
		### Configurations with a small cap
		for my $m ( $j+1 .. $l-1 ) {
			implies( dp( $s, $i, $j, $k, $l ),
				 var("in$i,$j,$m"),
				 var("in$j,$m,$l"),
				 sat_not(var("true")) # as above
			       );
		}
		### Configurations with a small cup
		for my $m ( $l+1 .. $j-1 ) {
			implies( dp( $s, $i, $j, $k, $l ),
				 sat_not(var("in$k,$l,$m")),
				 sat_not(var("in$l,$m,$j")),
				 sat_not(var("true")) # as above
			       );
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
#	warn join( " ", map {name($_)} @$clause), "\n";
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

## dp($s; $i, $j; $k, $l) returns a literal representing the DP
## variable "Is there a cup($i,$j)-cap($k,$l) configuration of $s
## total points?"  FYI, don't literally type semicolons.
sub dp {
	my( $s, $i, $j, $k, $l ) = @_;
	return var( "dp$s;$i,$j;$k,$l", "Is there a cup($i,$j)-cap($k,$l) configuration of $s total points?" );
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
