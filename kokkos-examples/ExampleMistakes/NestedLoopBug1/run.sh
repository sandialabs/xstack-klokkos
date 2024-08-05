
#!/bin/sh
for nrow in 100 200 300 400 1000
do
    for ncol in 100 200 300 400 1000
    do
        echo $nrow $ncol
        ../build/NestedLoopBug1 $nrow $ncol > NestedLoopBug1_$nrow\_$ncol.out
    done
done
