# CKKS-proof

because why not

## Design choices

We verify a version of CKKS that we know is provably secure.
There might be some differences between our CKKS model and the "real" implementations off the shelf.
There may even be some departures from theory papers.
This is not to be taken as a claim that the implementation or the known construction is not secure.

Our design choices and explanations are as follows.
* We use discrete Gaussians, while some implementations use rounded Gaussians.
* For convenience we treat some values such as noise bounds and discrete Gaussian variances as real numbers instead of floating point.
* During homomorphic evaluation we assume random rounding.
* We treat the initial encryption noise bound as an additional parameter. The literature mentions `6 * sigma`, but that has maybe `2 ^ -29` probability to go "wrong".
