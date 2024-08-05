
#!/bin/sh
for mysize in 100 1000 10000 100000
do
    echo $mysize
    ../build/ViewOutOfBoundBug1 $mysize > ViewOutOfBoundBug1_$mysize.out
done
