# BBChallenge Deciders

## News

**Update 06/03/22**. To improve the reproducibility of the results we have decided to lexicographically sort the main database `all_5_states_undecided_machines_with_global_header`. The first `14,322,029` undecided machines (47M time limit exceeded) were lexicographically sorted independently of the next `74,342,035` undecided machines (12k space limit exceeded). All indices files have been updated according to this order.

**Update 05/03/22**. 1 664 machines were decided by re-running the translated-cyler decider with higher parameters. Indeed we had discovered some more translated cyclers in the remaning undecided machines, such as machine #`36 496 615`. As of this day there remains **2 322 122** undecided machines in the database.

**Update 09/02/22**. 1 253 418 machines were decided thanks to the backward-reasoning decider:
[https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-backward-reasoning](https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-backward-reasoning). As of this day there remains **2 323 786** undecided machines in the database.

**Update 29/01/22**. 73 857 622 translated-cyclers were decided (among machines that exceeded space limit) thanks to the translated-cyclers decider:
[https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-translated-cyclers](https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-translated-cyclers). As of this day there remains **3 577 204** undecided machines in the database.

**Update 28/01/22**. 11 229 238 cyclers were decided (among machines that exceeded time limit) thanks to the cyclers decider: [https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-cyclers](https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-cyclers).


## Downloading the full database

The database computed by bbchallenge-seed is available here:

- [https://dna.hamilton.ie/tsterin/all_5_states_undecided_machines_with_global_header.zip](https://dna.hamilton.ie/tsterin/all_5_states_undecided_machines_with_global_header.zip)
- [ipfs://QmcgucgLRjAQAjU41w6HR7GJbcte3F14gv9oXcf8uZ8aFM](ipfs://QmcgucgLRjAQAjU41w6HR7GJbcte3F14gv9oXcf8uZ8aFM)
- [https://ipfs.prgm.dev/ipfs/QmcgucgLRjAQAjU41w6HR7GJbcte3F14gv9oXcf8uZ8aFM](https://ipfs.prgm.dev/ipfs/QmcgucgLRjAQAjU41w6HR7GJbcte3F14gv9oXcf8uZ8aFM)

The format of the database is described here: [https://github.com/bbchallenge/bbchallenge-seed](https://github.com/bbchallenge/bbchallenge-seed).

Database shasum: 
  - `all_5_states_undecided_machines_with_global_header.zip`: `2576b647185063db2aa3dc2f5622908e99f3cd40`.
  - `all_5_states_undecided_machines_with_global_header`: `e57063afefd900fa629cfefb40731fd083d90b5e`
  
## Downloading the index of currently undecided machines

An undecided index file is an ordered binary succession of uint32 (BigEndian) which corresponds to the IDs of the currently undecided machines in the above database.

The current size of the file is **9 295 144** bytes which corresponds to **(9 295 144)/4 = 2 323 786** machines. 

- [https://dna.hamilton.ie/tsterin/bb5_undecided_index](https://dna.hamilton.ie/tsterin/bb5_undecided_index)

Index file shasum: `f9e7f731532259691cf917ff35fd5051c00f1636`.
