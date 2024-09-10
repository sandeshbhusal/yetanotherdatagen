run_noaug: clean
	mvn package
	cd target/classes; java -cp '../../libs/*:.' edu.boisestate.datagen.App -s /tmp/sources/ -w /tmp/workdir -k true

run: clean
	mvn package
	cd target/classes; java -cp '../../libs/*:.' edu.boisestate.datagen.App -s /tmp/sources/ -w /tmp/workdir

clean:
	rm -rf /tmp/workdir/
	rm -rf /tmp/check_small_noaug_5it/
	mvn clean
