variable "aws_region" {
  description = "AWS region"
  type        = string
  default     = "us-east-2"
}

variable "instance_type" {
  description = "EC2 instance type"
  type        = string
  default     = "c8i.metal-96xl"  # 192 vCPUs (96 physical cores), 768GB RAM - bare metal
}

variable "availability_zone" {
  description = "Availability zone"
  type        = string
  default     = "us-east-2a"
}

variable "ami_id" {
  description = "Ubuntu 24.04 AMI ID"
  type        = string
  default     = "ami-06e3c045d79fd65d9"  # Ubuntu 24.04 in us-east-2
}

variable "root_volume_size" {
  description = "Root volume size in GB"
  type        = number
  default     = 100
}
