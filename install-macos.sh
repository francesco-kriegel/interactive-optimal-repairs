curl -L https://github.com/protegeproject/protege-distribution/releases/download/protege-5.6.3/Protege-5.6.3-platform-independent.zip --output Protege-5.6.3-platform-independent.zip
unzip Protege-5.6.3-platform-independent.zip
rm Protege-5.6.3-platform-independent.zip

curl -L https://download.oracle.com/graalvm/21/latest/graalvm-jdk-21_macos-x64_bin.tar.gz --output graalvm-jdk-21_macos-x64_bin.tar.gz
tar -xvzf graalvm-jdk-21_macos-x64_bin.tar.gz
rm graalvm-jdk-21_macos-x64_bin.tar.gz
mv $(ls -1 | grep "graalvm-jdk")/Contents/Home Protege-5.6.3/jre
rm -rf graalvm-jdk*

curl -L https://github.com/francesco-kriegel/interactive-optimal-repairs/releases/download/v0.1.5/interactive-optimal-repairs-0.1.5.jar --output Protege-5.6.3/plugins/interactive-optimal-repairs-0.1.5.jar

sed -i '' "s/#max_heap_size=8G/max_heap_size=16G/g" Protege-5.6.3/conf/jvm.conf

rm install-macos.sh

Protege-5.6.3/run.sh
