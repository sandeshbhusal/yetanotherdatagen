run:
	mvn clean
	mvn package
	cd target/classes; java -cp '../../libs/*:.' edu.boisestate.datagen.App -s /tmp/sources/ -w /tmp/workdir/ -i 15

clean:
	rm -rf /tmp/workdir/
	mvn clean
