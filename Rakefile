require 'bundler/setup'
require 'albacore'
require 'albacore/tasks/versionizer'

Albacore::Tasks::Versionizer.new :versioning

nugets_restore :restore do |p|
  p.out = 'src/packages'
  p.exe = 'buildsupport/NuGet.exe' 
end

build :build => [:versioning, :restore] do |b|
  b.sln = 'src/SharpLogic.sln'
end

directory 'build/pkg'

desc "package nugets"
nugets_pack :pack => ['build/pkg', :versioning, :build] do |p|
  p.files   = FileList['src/**/*.{fsproj,nuspec}'].
    exclude(/packages/)
  p.out     = 'build/pkg'
  p.exe     = 'buildsupport/NuGet.exe'
  p.version = ENV['NUGET_VERSION']
end

task :default => :pack
