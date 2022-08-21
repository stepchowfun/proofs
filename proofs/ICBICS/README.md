# I can't believe it can sort

This directory contains a proof of the correctness of the *I can't believe it can sort* algorithm [1]:

```
for i in [0, n) do
  for j in [0, n) do
    if A[i] < A[j] then
      swap A[i] and A[j]
```

[1] Stanley P. Y. Fung (2021). Is this the simplest (and most surprising) sorting algorithm ever? https://doi.org/10.48550/arXiv.2110.01111
