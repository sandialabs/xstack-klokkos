
#!/bin/sh
for sample in 100 1000 10000 100000
do
   echo $sample
   ../build/DeepSoftCopyBug1 $sample > DeepSoftCopyBug1_$sample.out
done
