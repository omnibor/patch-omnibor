cp hello1.orig hello1.c
cp hello2.orig hello2.c
cp hello3.orig hello3.c
../../../../patch-2.7.6/src/patch --omnibor=dir -p0 -i hello.patch
