# XSets : coherent interface of MSets

XSets are the extended MSets in the standard library.
(W)Sets in MSets are enough for users.
However, some of the functions (signatures) in (W)RawSets miss some parameters.
For examples, fold_spec, filter_spec, for_all_spec, exists_spec, partition_spec1, 2, elements_spec1, choose_spec1 and 2 do not requires "Ok s", which is invariant in RawSets.

Also, specs for filter and partition requires "compatb", but sometimes it is difficult to prove the filtering function is "compatb".
(It is the case when I made [XSetRepresentative](https://github.com/chiguri/XSetRepresentative))
(W)Sets in XSets have weaker specs for filter and partitions.



## Why don't you make this as patch for MSets?
In MSets, there is a module for mutual translations with FSets, an old "set libraries".
Unfortunately, (W)Sets in XSets are incompatible with those in (M)Sets, and of cource not with FSets.
The translation from FSets to MSets prevents me from making patches.


