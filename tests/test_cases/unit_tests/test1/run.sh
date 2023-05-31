cp hello.orig hello.c
../../../../patch-2.7.6/src/patch -p0 --omnibor -i hello1.patch
cp hello.c hello.c.1
../../../../patch-2.7.6/src/patch -p0 --omnibor -i hello2.patch
cp hello.c hello.c.2
../../../../patch-2.7.6/src/patch -p0 --omnibor -i hello3.patch
cp hello.c hello.c.3
../../../../patch-2.7.6/src/patch -p0 --omnibor -i hello4.patch
cp hello.c hello.c.4
../../../../patch-2.7.6/src/patch -p0 --omnibor -i hello5.patch
cp hello.c hello.c.5
