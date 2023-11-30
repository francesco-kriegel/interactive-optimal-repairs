curl -LJO https://github.com/protegeproject/protege-distribution/releases/download/protege-5.6.3/Protege-5.6.3-platform-independent.zip --output Protege-5.6.3-platform-independent.zip
unzip Protege-5.6.3-platform-independent.zip
rm Protege-5.6.3-platform-independent.zip

curl https://download.oracle.com/graalvm/21/latest/graalvm-jdk-21_macos-x64_bin.tar.gz --output graalvm-jdk-21_macos-x64_bin.tar.gz
tar -xvzf graalvm-jdk-21_macos-x64_bin.tar.gz
rm graalvm-jdk-21_macos-x64_bin.tar.gz
mv graalvm-jdk-21.0.1+12.1/Contents/Home Protege-5.6.3/jre
rm -rf graalvm-jdk-21.0.1+12.1

curl -LJO https://github.com/francesco-kriegel/interactive-optimal-repairs/releases/download/v0.1.0/interactive-optimal-repairs-0.1.0.jar --output Protege-5.6.3/plugins/interactive-optimal-repairs-0.1.0.jar

sed -i '' "s/#max_heap_size=8G/max_heap_size=16G/g" Protege-5.6.3/conf/jvm.conf

Protege-5.6.3/run.sh
