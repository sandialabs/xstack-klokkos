
#!/bin/sh
for sample in 100 1000 10000 100000
do
  for seed in 1 2 3 4 5
  do
	echo $seed
	echo $sample
        ./NotUsingAtomicsBug $sample $seed > NotUsingAtomicsBug_$sample\_$seed.out
  done
done
