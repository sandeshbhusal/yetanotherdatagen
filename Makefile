run:
	mvn clean
	mvn package
	cd target/classes; java -cp '../../libs/*:.' edu.boisestate.datagen.App -s /tmp/sources/ -w /tmp/workdir/

clean:
	mvn clean
