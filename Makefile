all: pom.xml src/
	mvn clean compile
	mvn dependency:copy-dependencies

run: all
	cd target/classes; java -cp '../dependency/*:.' edu.boisestate.datagen.App -s /tmp/sources/ -w /tmp/workdir/

clean:
	mvn clean
