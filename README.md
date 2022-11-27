# vsr-tlaplus
TLA+ specifications related to Viewstamped Replication.

The following specifications exist:
- Viewstamped Replication Revisited paper.
    - VSR.tla is based solely on the paper and does not implement
      any fixes to protocol defects from this paper.

## State transfer defect

To reproduce the state transfer defect of the revisited paper, set the following
constant values:
```    
    ReplicaCount = 3
    ClientCount = 1
    Values = {v1, v2, v3}
    StartViewOnTimerLimit = 3
```

When running with model checking, ensure you have at least 500GB of disk available and a large number of cores, else you'll ever run out of disk or have to wait multiple days.

Alternatively, use simulation mode, which has a good chance of hitting it sooner.