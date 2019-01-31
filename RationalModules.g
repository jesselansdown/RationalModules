##############################################################
#
# Jesse Lansdown 2019
#
##############################################################
LoadPackage("gauss");;

__RationalModules__ConvertToRational := function(x, p)
	# This can be done better...
	local j, i, y;
	y:=[1..Size(x)];;
	for i in [1..Size(x)] do
		y[i]:=IntFFE(x[i]);;
	od;
	return y;
end;


__RationalModules__ConvertModuleBasis := function(a, p)
	local mat, i;;
	mat:=[];;
	for i in a do
		Add(mat, __RationalModules__ConvertToRational(i, p));;
	od;
	return mat;
end;

__RationalModules__pullbackval := function(x, d, p)
	return x*d mod p;
end;

__RationalModules__pullback := function(undetermined, prime, max)
	local n, i, s;;
	n := Size(undetermined);
	for i in [1 .. max] do
		s := List([1..n], t -> __RationalModules__pullbackval(undetermined[t], i, prime[t] ));
		if Size(Set(s))=1 then
			return s[1]/i;
		fi;
	od;
	for i in [1 .. max] do
		s := List([1..n], t -> __RationalModules__pullbackval(-undetermined[t], i, prime[t] ));
		if Size(Set(s))=1 then
			return -s[1]/i;
		fi;
	od;
	#Print("Failed in: __RationalModules__pullback\n");
	return fail;
end;


__RationalModules__pullall:= function(vals, primes, max)
	local n, out, i, undetermined,s;
	n:=Size(vals[1]);
	out :=[];
	for i in [1 .. n] do
		undetermined := List(vals, t -> t[i]);;
		s := __RationalModules__pullback(undetermined, primes, max);
		if not s = fail then
			Add(out, s);
		else
			#Print("Failed in: __RationalModules__pullall\n");
			#Print(i, "\n");
			return fail;
		fi;
	od;
	return out;
end;


__RationalModules__entryfinder := function(entries, basis)
	local out, x, i, j;;
	out:=[];
	for x in entries do
		i := First([1 .. Size(basis)], t -> x in basis[t]);;
		j := First([1 .. Size(basis[i])], t -> basis[i][t]=x);
		Add(out, [i,j]);
	od;
	return out;
end;


__RationalModules__ModuleOverRationals := function(bases, primes, max)
	local entries, inds, vals, i, actualvals, b, x, j, k;;
	entries:= Set(Flat(bases[1]));;
	inds := __RationalModules__entryfinder(entries, bases[1]);;
	vals:=[];
	for i in [1 .. Size(bases)] do
		Add(vals, List(inds, t -> bases[i][t[1]][t[2]]));
	od;
	actualvals := __RationalModules__pullall(vals, primes, max);;
	if actualvals = fail then
		#Print("Failed in: __RationalModules__ModuleOverRationals\n");
		return fail;
	else
		b:= MutableCopyMat(StructuralCopy(bases[1]));;
		for k in [1 .. Size(inds)] do
			x:=b[inds[k][1]][inds[k][2]];;
			for i in [1 .. Size(b)] do
				for j in [1 .. Size(b[i])] do
					if b[i][j]=x then
						b[i][j]:= actualvals[k];
					fi;
				od;
			od;
		od;
	fi;
	return b;
end;


__RationalModules__BasesMinimalSubmodulesOverRationals := function(g_perm, primes, max)
	local bases, p, m, subs, subs2, b, basis, out, a, bases2, i;
	# TODO:
	# Put a check to discard submodules which don't properly decompose.
	# Put a check that the submodules correspond to each other - sort by dimension, plus additional checks
	# Put a check the output are indeed submodules
	# Return in the format which MTX uses.
	bases:=[];
	for p in primes do
		m:=PermutationGModule(g_perm, GF(p));
		subs:=MTX.BasesMinimalSubmodules(m);
		subs2:=[];;
		for b in subs do
			basis := EchelonMat(__RationalModules__ConvertModuleBasis(b, p)).vectors;;
			Add(subs2, basis);;
		od;
		Add(bases, subs2);
	od;
	out:=[];;
	for i in [1 .. Size(bases[1])] do
		bases2 := List(bases, t -> t[i]);;
		a := __RationalModules__ModuleOverRationals(bases2, primes, max);;
		if a = fail then
			#Print("Failed in: __RationalModules__BasesMinimalSubmodulesOverRationals\n");
			#Print(i, "\n");
			return fail;
		else
			Add(out, a);
		fi;
	od;
	return out;
end;







__RationalModules__BasesMinimalSubmodulesOverRationals := function(g_perm, primes, max)
	local bases, p, m, subs, subs2, b, basis, out, a, bases2, i, dims, subs3, iter, next, k;
	# TODO:
	# Put a check to discard submodules which don't properly decompose.
	# Put a check that the submodules correspond to each other - sort by dimension, plus additional checks
	# Put a check the output are indeed submodules
	# Return in the format which MTX uses.
	bases:=[];
	for p in primes do
		m:=PermutationGModule(g_perm, GF(p));
		subs:=MTX.BasesMinimalSubmodules(m);
		subs2:=[];;
		for b in subs do
			basis := EchelonMat(__RationalModules__ConvertModuleBasis(b, p)).vectors;;
			Add(subs2, basis);;
		od;
		Add(bases, subs2);
		if Size(Set(List(bases, Size)))<>1 then
			Print(List(bases, Size),"x\c");
			return fail;
		fi;
	od;
	Print(List(bases, Size),"+\c");
	out:=[];;
	dims:=Set(List(bases[1], Size));;
	subs3:=[];
	for i in dims do
		Add(subs3, List(bases, t -> Filtered(t, x -> Size(x)=i)));
	od;
	for i in [1 .. Size(subs3)] do
		d := Size(subs3[i][1]);;
		for j in [1 .. d] do
			iter := IteratorOfTuples( [1 .. Size(subs3[i])], Size(primes));
			while not IsDoneIterator(iter) do
				next := NextIterator(iter);;
				bases2 := subs3[i]{next};;
				bases2 := List(bases2, t -> t[1]);;
				a := __RationalModules__ModuleOverRationals(bases2, primes, max);;
				if a <> fail then
					Add(out, a);;
					for k in [1.. Size(subs3[i])] do
						Remove(subs3[i][k], next[k]);
					od;
					break;
				fi;
			od;
			if a = fail then
				return fail;
			fi;
		od;
	od;
	return out;
end;



BasesMinimalSubmodulesOverRationals := function(g_perm)
	local primes, max, primeoptions, out;
	# TODO:
	# Put controls over primes and max, increasing them if needed.
	# Increase the magnitude of primes depending on g_perm, and increase number adaptively.
	# Make this a method for MTX when called with "Rationals"
	primeoptions:=[
		[ 97, 89, 83, 79, 73 ],
		[ 1009, 1013, 1019, 1021, 1031],
		[10007, 10009, 10037, 10039],
		[ 100003, 100019, 100043 ],
		[ 1000003, 1000033, 1000037],
		[ 10000019, 10000079, 10000103],
		[ 100000007, 100000037, 100000039],
		[ 1000000007, 1000000009, 1000000021],
		[ 10000000019, 10000000033, 10000000061 ],
		[ 100000000003, 100000000019, 100000000057 ],
		[ 1000000000039, 1000000000061, 1000000000063 ]
	];;
	max := 100;
	for primes in primeoptions do
		#max:=max*10;;
		out := __RationalModules__BasesMinimalSubmodulesOverRationals(g_perm, primes, max);
		if out <> fail then
			return out;
		else
			Print("Failed to compute - increasing range of primes.\n");
		fi;
	od;
	Print("Failed to compute - Yeah, you're gonna need bigger primes...\n");
	return out;
end;







__RationalModules__BasesSubmodulesOverRationals := function(g_perm, primes, max)
	local bases, p, m, subs, subs2, b, basis, out, a, bases2, i;
	# TODO:
	# Put a check to discard submodules which don't properly decompose.
	# Put a check that the submodules correspond to each other - sort by dimension, plus additional checks
	# Put a check the output are indeed submodules
	# Return in the format which MTX uses.
	bases:=[];
	for p in primes do
		m:=PermutationGModule(g_perm, GF(p));
		subs:=MTX.BasesSubmodules(m);
		subs2:=[];;
		for b in subs do
			basis := EchelonMat(__RationalModules__ConvertModuleBasis(b, p)).vectors;;
			Add(subs2, basis);;
		od;
		Add(bases, subs2);
	od;
	out:=[];;
	for i in [1 .. Size(bases[1])] do
		bases2 := List(bases, t -> t[i]);;
		a := __RationalModules__ModuleOverRationals(bases2, primes, max);;
		if a = fail then
			#Print("Failed in: __RationalModules__BasesMinimalSubmodulesOverRationals\n");
			#Print(i, "\n");
			return fail;
		else
			Add(out, a);
		fi;
	od;
	return out;
end;


BasesSubmodulesOverRationals := function(g_perm)
	local primes, max, out;
	# TODO:
	# Put controls over primes and max, increasing them if needed.
	# Increase the magnitude of primes depending on g_perm, and increase number adaptively.
	# Make this a method for MTX when called with "Rationals"
	primes:=[ 97, 89, 83, 79, 73 ];;
	# Implement some method to determine which primes to use. Perhaps the first 5 primes larger than the vectorspace dimension?
	max := 1000;
	# Implement some method of choosing max.
	out := __RationalModules__BasesMinimalSubmodulesOverRationals(g_perm, primes, max);
	return out;
end;
