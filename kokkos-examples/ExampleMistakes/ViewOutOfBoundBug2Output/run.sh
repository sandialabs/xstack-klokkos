
#!/bin/sh
for nrow in 100 200 300 400  
do
    for ncol in 100 200 300 400
    do
        echo $nrow $ncol
        ../build/ViewOutOfBoundBug2 $nrow $ncol > ViewOutOfBoundBug2_$nrow\_$ncol.out
    done
done
